use crate::bitset::BitSetT;
use crate::fixed_bitset;
use crate::pool::Pool;
use crate::sat::*;
use itertools::Either;
use rand::prelude::*;
use rand_pcg::Pcg64;
use std::cell::RefCell;
use std::collections::BTreeMap;

pub trait ConfigT: Sized {
    type BitSet: BitSetT + Clone;

    fn choose_variable(state: &mut State<Self>) -> Option<usize>;

    const DEBUG: bool;
    const USE_BACKTRACK_STATE: bool;
}

#[macro_export]
macro_rules! debug {
    // With optional writer
    ($writer:expr, $($arg:tt)+) => {
        if Config::DEBUG {
            match $writer {
                Some(ref w) => {
                    use std::fmt::Write as _;
                    let _ = writeln!(w.borrow_mut(), $($arg)+);
                }
                None => {
                    eprintln!($($arg)+);
                }
            }
        }
    };

    // Fallback: no writer provided
    ($($arg:tt)+) => {
        if Config::DEBUG {
            eprintln!($($arg)+);
        }
    };
}

#[derive(Clone, Copy, Debug)]
enum Reason {
    Decision(Literal),
    ClauseIdx(usize),
}

struct TrailEntry<BitSet: BitSetT> {
    literal: Literal,
    decision_level: usize,
    reason: Reason,
    satisfied_clauses: Option<BitSet>,
    pub continue_: bool,
}

impl<BitSet: BitSetT> TrailEntry<BitSet> {
    pub fn is_from_decision_point(&self) -> bool {
        matches!(self.reason, Reason::Decision(_))
    }
}

pub struct State<Config: ConfigT> {
    immediate_result: Option<SatResult>,
    all_variables: Config::BitSet,
    assignments: Config::BitSet,
    clauses: Vec<Clause<Config::BitSet>>,
    trail: Vec<TrailEntry<Config::BitSet>>,
    unassigned_variables: Config::BitSet,
    unsatisfied_clauses: Config::BitSet,
    clauses_by_var: Vec<Config::BitSet>,
    trail_entry_idx_by_var: Vec<usize>,
    scratch_clause_bitset: Option<Config::BitSet>,
    scratch_variable_bitset: Option<Config::BitSet>,
    decision_level: usize,
    next_literal: Option<Literal>,
    bitset_pool: Pool<Config::BitSet>,
    iterations: usize,
    rng: Pcg64,
    debug_writer: Option<RefCell<Box<dyn std::fmt::Write>>>,
}

#[derive(Clone, Copy, Debug)]
struct ClauseIdx(usize);

#[derive(Clone, Copy)]
struct TrailIdx(usize);

#[derive(Clone, Copy)]
enum UnitPropagationResult {
    FinishedUnitPropagation,
    Contradiction(ClauseIdx),
    NothingToPropagate,
}

#[derive(Clone, Copy, Debug)]
enum Action {
    Unsat,
    FinishedUnitPropagation,
    Continue(Literal, bool),
    Contradiction(usize),
}

impl<Config: ConfigT> State<Config> {
    fn assignments(&self) -> BTreeMap<usize, bool> {
        self.all_variables
            .iter()
            .map(|var| (var, self.assignments.contains(var)))
            .collect()
    }

    fn try_get_unit_literal(&self, clause: &Clause<Config::BitSet>) -> Option<Literal> {
        match self
            .unassigned_variables
            .intersect_first_set(&clause.variables)
        {
            // exactly one unset -> unit
            Some(var) => {
                match self
                    .unassigned_variables
                    .intersect_first_set_ge(&clause.variables, var + 1)
                {
                    Some(_) => None,
                    None => {
                        // found a unit clause
                        Some(Literal::new(var, !clause.negatives.contains(var)))
                    }
                }
            }
            None => None,
        }
    }

    // TODO: maybe not needed
    fn clause_is_satisfied(&self, clause: &Clause<Config::BitSet>) -> bool {
        clause
            .variables
            .iter_difference(&self.unassigned_variables)
            .any(|var| self.assignments.contains(var) != clause.negatives.contains(var))
    }

    fn first_unit_clause(&self) -> Option<(Literal, ClauseIdx)> {
        self.unsatisfied_clauses.iter().find_map(|clause_idx| {
            let clause = &self.clauses[clause_idx];
            self.try_get_unit_literal(clause)
                .map(|literal| (literal, ClauseIdx(clause_idx)))
        })
    }

    fn clauses_mut(&mut self, literal: Literal) -> Option<&mut Config::BitSet> {
        if literal.variable() < self.clauses_by_var.len() {
            Some(&mut self.clauses_by_var[literal.variable()])
        } else {
            None
        }
    }

    fn clauses(&self, literal: Literal) -> Option<&Config::BitSet> {
        if literal.variable() < self.clauses_by_var.len() {
            Some(&self.clauses_by_var[literal.variable()])
        } else {
            None
        }
    }

    fn would_be_contradiction(&self, literal: Literal) -> Option<ClauseIdx> {
        self.clauses(literal)?
            .iter_intersection(&self.unsatisfied_clauses)
            .find_map(|clause_idx| {
                let clause = &self.clauses[clause_idx];
                let literal_in_unit = self.try_get_unit_literal(clause)?;
                if literal_in_unit.variable() == literal.variable()
                    && literal_in_unit.value() != literal.value()
                {
                    if Config::DEBUG {
                        let s = self.clause_string(ClauseIdx(clause_idx));
                        debug!(
                            self.debug_writer,
                            "would be contradiction with clause {:?} for literal {}",
                            s,
                            literal.to_string()
                        );
                    }
                    Some(ClauseIdx(clause_idx))
                } else {
                    None
                }
            })
    }

    fn undo_entry(&mut self, trail_entry: &mut TrailEntry<Config::BitSet>) {
        let satisfied_clauses = std::mem::take(&mut trail_entry.satisfied_clauses);
        match satisfied_clauses {
            None => (),
            Some(clauses) => {
                self.unsatisfied_clauses.union_with(&clauses);
                self.bitset_pool.release(clauses);
            }
        };
        self.trail_entry_idx_by_var[trail_entry.literal.variable()] = usize::MAX;
        self.unassigned_variables
            .set(trail_entry.literal.variable());
    }

    fn satisfy_clauses(&mut self, trail_entry: &TrailEntry<Config::BitSet>) -> Config::BitSet {
        let literal = trail_entry.literal;
        let var = literal.variable();
        let mut scratch_clause_bitset = std::mem::take(&mut self.scratch_clause_bitset).unwrap();
        scratch_clause_bitset.clear_all();
        let clauses = self.clauses(literal);
        match clauses {
            None => (),
            Some(clauses) => scratch_clause_bitset.intersect(clauses, &self.unsatisfied_clauses),
        }
        let mut newly_set = self.bitset_pool.acquire(|| Config::BitSet::create());
        for clause_idx in scratch_clause_bitset.iter() {
            let clause = &self.clauses[clause_idx];
            let desired_value = !clause.negatives.contains(var);
            if desired_value == literal.value() {
                newly_set.set(clause_idx);
                self.unsatisfied_clauses.clear(clause_idx);
            }
        }
        self.scratch_clause_bitset = Some(scratch_clause_bitset);
        debug!(
            self.debug_writer,
            "satisfy_clauses: clauses satisfied by literal {}: {}",
            literal.to_string(),
            newly_set
                .iter()
                .map(|idx| self.clause_string(ClauseIdx(idx)))
                .collect::<Vec<_>>()
                .join(", ")
        );
        newly_set
    }

    fn add_to_trail(&mut self, mut trail_entry: TrailEntry<Config::BitSet>) {
        debug!(
            self.debug_writer,
            "adding to trail at decision level {}: {}",
            trail_entry.decision_level,
            trail_entry.literal.to_string()
        );
        let literal = trail_entry.literal;
        let var = literal.variable();
        if literal.value() {
            self.assignments.set(var);
        } else {
            self.assignments.clear(var);
        }
        assert!(
            self.trail_entry_idx_by_var[var] == usize::MAX,
            "trail entry for var {} already exists: {:?}",
            var,
            self.trail_entry_idx_by_var[var]
        );
        self.trail_entry_idx_by_var[var] = self.trail.len();
        self.unassigned_variables.clear(var);
        trail_entry.satisfied_clauses = Some(self.satisfy_clauses(&trail_entry));
        self.trail.push(trail_entry);
    }

    fn unit_propagate_internal(&mut self) -> UnitPropagationResult {
        if let Some((literal, clause_idx)) = self.first_unit_clause() {
            self.with_unit_clause(literal, clause_idx)
        } else {
            UnitPropagationResult::FinishedUnitPropagation
        }
    }

    fn clause_string(&self, clause_idx: ClauseIdx) -> String {
        self.clauses[clause_idx.0].to_string()
    }

    fn with_unit_clause(
        &mut self,
        literal: Literal,
        clause_idx: ClauseIdx,
    ) -> UnitPropagationResult {
        debug!(
            self.debug_writer,
            "found unit clause: {:?} in clause ({:?})",
            literal,
            self.clause_string(clause_idx)
        );
        let decision_level = self.decision_level;
        let trail_entry = TrailEntry {
            literal,
            decision_level,
            reason: Reason::ClauseIdx(clause_idx.0),
            satisfied_clauses: None,
            continue_: false,
        };
        let conf = self.would_be_contradiction(literal);
        self.add_to_trail(trail_entry);
        if let Some(conflict) = conf {
            UnitPropagationResult::Contradiction(conflict)
        } else {
            self.unit_propagate_internal()
        }
    }

    fn unit_propagate(&mut self) -> UnitPropagationResult {
        if let Some((literal, clause_idx)) = self.first_unit_clause() {
            self.with_unit_clause(literal, clause_idx)
        } else {
            UnitPropagationResult::NothingToPropagate
        }
    }

    fn literal_in_trail_for_var(&self, var: usize) -> Literal {
        let idx = self.trail_entry_idx_by_var[var];
        if idx == usize::MAX {
            panic!("no entry for var {}", var);
        }
        self.trail[idx].literal
    }

    fn iter_reason_literals<'a>(&'a self, reason: Reason) -> impl Iterator<Item = Literal> + 'a {
        match reason {
            Reason::Decision(lit) => Either::Left(std::iter::once(lit)),
            Reason::ClauseIdx(idx) => Either::Right(self.clauses[idx].iter_literals()),
        }
    }

    fn only_one_at_level(&self, clause: &Clause<Config::BitSet>) -> bool {
        clause
            .iter_literals()
            .filter(|&lit| {
                let idx = self.trail_entry_idx_by_var[lit.variable()];
                self.trail[idx].decision_level == self.decision_level
            })
            .count()
            == 1
    }

    fn second_highest_decision_level(&self, clause: &Clause<Config::BitSet>) -> usize {
        let mut max1 = 0;
        let mut max2 = 0;
        for lit in clause.iter_literals() {
            let var = lit.variable();
            let idx = self.trail_entry_idx_by_var[var];
            let entry = &self.trail[idx];
            if entry.decision_level > max1 {
                max2 = max1;
                max1 = entry.decision_level;
            } else if entry.decision_level > max2 && entry.decision_level < max1 {
                max2 = entry.decision_level;
            }
        }
        max2
    }

    fn next_entry_for_learned_clause(&self, clause: &Clause<Config::BitSet>) -> Option<usize> {
        clause
            .iter_literals()
            .filter_map(|lit| {
                let idx = self.trail_entry_idx_by_var[lit.variable()];
                let entry = &self.trail[idx];
                if !entry.is_from_decision_point() && entry.decision_level == self.decision_level {
                    Some(idx)
                } else {
                    None
                }
            })
            .max()
    }

    fn learn_clause_from_failure(
        &mut self,
        failed_clause_idx: ClauseIdx,
    ) -> (Clause<Config::BitSet>, usize) {
        let mut learned = {
            let mut variables = self.bitset_pool.acquire(|| Config::BitSet::create());
            let mut negatives = self.bitset_pool.acquire(|| Config::BitSet::create());
            variables.clear_all();
            negatives.clear_all();
            variables.union_with(&self.clauses[failed_clause_idx.0].variables);
            negatives.union_with(&self.clauses[failed_clause_idx.0].negatives);
            Clause {
                variables,
                negatives,
            }
        };
        loop {
            match self.next_entry_for_learned_clause(&learned) {
                None => assert!(false),
                Some(idx) => {
                    let entry = &self.trail[idx];
                    let lit = entry.literal;
                    match entry.reason {
                        Reason::Decision(_) => assert!(false),
                        Reason::ClauseIdx(clause_idx) => {
                            let resolve_with = &self.clauses[clause_idx];
                            debug!(
                                self.debug_writer,
                                "Resolving learned {} with {} on {}",
                                learned.to_string(),
                                resolve_with.to_string(),
                                lit.variable()
                            );

                            learned.resolve_exn(resolve_with, lit.variable());

                            if self.only_one_at_level(&learned) {
                                break;
                            }
                        }
                    }
                }
            }
        }
        let backtrack_level = self.second_highest_decision_level(&learned);
        debug!(
            self.debug_writer,
            "learned clause: {:?} from failed clause {:?}, backtrack level: {}",
            learned.to_string(),
            self.clause_string(failed_clause_idx),
            backtrack_level
        );
        (learned, backtrack_level)
    }

    fn remove_from_trail_helper(&mut self, remove_greater_than: Option<usize>) -> Option<Literal> {
        let mut trail_entry: Option<TrailEntry<Config::BitSet>> = None;
        loop {
            let finished = self.trail.is_empty()
                || match remove_greater_than {
                    None => trail_entry
                        .as_ref()
                        .map(|trail_entry| trail_entry.continue_)
                        .unwrap_or(false),
                    Some(decision_level) => self
                        .trail
                        .last()
                        .map(|last_entry| last_entry.decision_level <= decision_level)
                        .unwrap_or(false),
                };
            if finished {
                break;
            }
            let mut this_trail_entry = self.trail.pop().unwrap();
            self.undo_entry(&mut this_trail_entry);
            trail_entry = Some(this_trail_entry);
        }
        self.decision_level = if self.trail.is_empty() {
            0
        } else {
            self.trail.last().unwrap().decision_level
        };
        match trail_entry {
            None => None,
            Some(last_entry) if last_entry.continue_ => Some(last_entry.literal.negate()),

            Some(_) => None,
        }
    }

    fn backtrack(&mut self, failed_clause_idx: ClauseIdx) -> Option<Literal> {
        let (learned_clause, remove_greater_than) =
            self.learn_clause_from_failure(failed_clause_idx);
        for lit in learned_clause.iter_literals() {
            let len = self.clauses.len();
            self.clauses_mut(lit).iter_mut().for_each(|clauses| {
                clauses.set(len);
            });
        }
        self.unsatisfied_clauses.set(self.clauses.len());
        self.clauses.push(learned_clause);
        let mut res = self.remove_from_trail_helper(Some(remove_greater_than));

        if !Config::USE_BACKTRACK_STATE {
            None
        } else {
            loop {
                match res {
                    None => (),
                    res => break res,
                }
                res = self.remove_from_trail_helper(None);
                if self.trail.is_empty() {
                    break None;
                }
            }
        }
    }

    fn react(&mut self, action: Action) -> StepResult {
        debug!(
            self.debug_writer,
            "reacting to action: {:?} at decision level {}", action, self.decision_level
        );
        match action {
            Action::Unsat => {
                self.immediate_result = Some(SatResult::Unsat);
                StepResult::Done(SatResult::Unsat)
            }
            Action::FinishedUnitPropagation => StepResult::Continue,
            Action::Continue(literal, continue_flag) => {
                let trail_entry = TrailEntry {
                    literal,
                    decision_level: self.decision_level,
                    reason: Reason::Decision(literal),
                    satisfied_clauses: None,
                    continue_: continue_flag,
                };
                self.add_to_trail(trail_entry);
                StepResult::Continue
            }
            Action::Contradiction(_) if self.decision_level == 0 => {
                StepResult::Done(SatResult::Unsat)
            }
            Action::Contradiction(failed_idx) => {
                let back = self.backtrack(ClauseIdx(failed_idx));

                if !Config::USE_BACKTRACK_STATE {
                    StepResult::Continue
                } else {
                    match back {
                        None => StepResult::Done(SatResult::Unsat),
                        Some(lit) => {
                            self.next_literal = Some(lit);
                            StepResult::Continue
                        }
                    }
                }
            }
        }
    }

    fn make_decision(&mut self, literal_override: Option<Literal>) -> StepResult {
        if let Some(lit) = self.next_literal.take() {
            return self.react(Action::Continue(lit, false));
        }
        match Config::choose_variable(self) {
            None => {
                let assignments = self.assignments();
                let res = SatResult::Sat(assignments);
                StepResult::Done(res)
            }
            Some(var) => {
                self.decision_level += 1;
                let lit = literal_override.unwrap_or_else(|| Literal::new(var, true));
                self.react(Action::Continue(lit, true))
            }
        }
    }

    pub fn step(&mut self, literal_override: Option<Literal>) -> StepResult {
        self.iterations += 1;
        if let Some(res) = self.immediate_result.take() {
            return StepResult::Done(res);
        }
        match self.unit_propagate() {
            UnitPropagationResult::NothingToPropagate => self.make_decision(literal_override),
            UnitPropagationResult::FinishedUnitPropagation => StepResult::Continue,
            UnitPropagationResult::Contradiction(ClauseIdx(idx)) => {
                self.react(Action::Contradiction(idx))
            }
        }
    }

    pub fn run(&mut self) -> SatResult {
        loop {
            match self.step(None) {
                StepResult::Done(SatResult::Unsat) => return SatResult::Unsat,
                StepResult::Done(SatResult::Sat(res)) => {
                    assert!(satisfies(&self.clauses, &res));
                    return SatResult::Sat(res);
                }
                StepResult::Continue => continue,
            }
        }
    }

    pub fn new_with_pool_and_debug_writer<Writer: std::fmt::Write + 'static>(
        formula: Formula<Config::BitSet>,
        mut bitset_pool: Pool<Config::BitSet>,
        debug_writer: Option<Writer>,
    ) -> Self {
        let Formula {
            max_var,
            vars,
            clauses,
            literal_counts: _,
        } = formula;
        let num_vars = max_var + 1;
        let mut variables_bitset = Config::BitSet::create();
        let mut clauses_by_var = vec![];

        for var in vars {
            variables_bitset.set(var);
        }

        for _ in 0..num_vars {
            clauses_by_var.push(bitset_pool.acquire(|| Config::BitSet::create()));
        }

        let mut instantly_unsat = false;

        for (idx, clause) in clauses.iter().enumerate() {
            if clause.variables.is_empty() {
                instantly_unsat = true;
            }
            clause.iter_literals().for_each(|lit| {
                clauses_by_var[lit.variable()].set(idx);
            });
        }
        let immediate_result = if instantly_unsat {
            Some(SatResult::Unsat)
        } else if clauses.is_empty() {
            Some(SatResult::Sat(BTreeMap::new()))
        } else {
            None
        };
        let debug_writer = match debug_writer {
            None => None,
            Some(w) => {
                let b: Box<dyn std::fmt::Write> = Box::new(w);
                Some(RefCell::new(b))
            }
        };
        let mut unsatisfied_clauses = Config::BitSet::create();
        unsatisfied_clauses.set_between(0, clauses.len());
        let all_variables = variables_bitset.clone();
        let unassigned_variables = variables_bitset;
        let rng = Pcg64::seed_from_u64(1);
        State {
            immediate_result,
            all_variables,
            assignments: Config::BitSet::create(),
            clauses,
            trail: Vec::with_capacity(64),
            unassigned_variables,
            unsatisfied_clauses,
            clauses_by_var,
            trail_entry_idx_by_var: vec![usize::MAX; num_vars],
            scratch_clause_bitset: Some(bitset_pool.acquire(|| Config::BitSet::create())),
            scratch_variable_bitset: Some(bitset_pool.acquire(|| Config::BitSet::create())),
            decision_level: 0,
            next_literal: None,
            bitset_pool,
            iterations: 0,
            rng,
            debug_writer,
        }
    }

    pub fn new_with_debug_writer<Writer: std::fmt::Write + 'static>(
        formula: Formula<Config::BitSet>,
        debug_writer: Option<Writer>,
    ) -> Self {
        Self::new_with_pool_and_debug_writer(formula, Pool::new(), debug_writer)
    }

    pub fn new(formula: Formula<Config::BitSet>) -> Self {
        Self::new_with_debug_writer::<String>(formula, None)
    }

    pub fn new_from_vec(formula: Vec<Vec<isize>>) -> Self {
        Self::new_from_vec_with_debug_writer::<String>(formula, None)
    }

    pub fn new_from_vec_with_debug_writer<Writer: std::fmt::Write + 'static>(
        formula: Vec<Vec<isize>>,
        debug_writer: Option<Writer>,
    ) -> Self {
        let mut bitset_pool = Pool::new();
        let formula = Formula::new(formula, &mut bitset_pool);
        Self::new_with_pool_and_debug_writer(formula, bitset_pool, debug_writer)
    }

    pub fn solve_with_debug_writer<Writer: std::fmt::Write + 'static>(
        formula: Vec<Vec<isize>>,
        debug_writer: Option<Writer>,
    ) -> SatResult {
        let mut state = Self::new_from_vec_with_debug_writer(formula, debug_writer);
        state.run()
    }

    pub fn solve(formula: Vec<Vec<isize>>) -> SatResult {
        Self::solve_with_debug_writer::<String>(formula, None)
    }
}

pub struct FirstSetConfig {}
pub struct RandomConfig {}
pub struct FirstSetConfigDebug {}
pub struct RandomConfigDebug {}

impl ConfigT for FirstSetConfig {
    type BitSet = fixed_bitset::BitSet<Vec<[usize; 1]>, 1>;

    fn choose_variable(state: &mut State<Self>) -> Option<usize> {
        state.unassigned_variables.first_set()
    }

    const DEBUG: bool = false;
    const USE_BACKTRACK_STATE: bool = true;
}

impl ConfigT for FirstSetConfigDebug {
    type BitSet = fixed_bitset::BitSet<Vec<[usize; 1]>, 1>;

    fn choose_variable(state: &mut State<Self>) -> Option<usize> {
        state.unassigned_variables.first_set()
    }

    const DEBUG: bool = true;
    const USE_BACKTRACK_STATE: bool = true;
}

fn choose_random_variable<T: ConfigT>(state: &mut State<T>) -> Option<usize> {
    let len = state.unassigned_variables.count();
    if len == 0 {
        None
    } else {
        let num = state.rng.random_range(0..len);
        match state.unassigned_variables.nth(num) {
            Some(var) => Some(var),
            None => panic!("unassigned_variables should have been non-empty, but was empty"),
        }
    }
}

impl ConfigT for RandomConfig {
    type BitSet = fixed_bitset::BitSet<Vec<[usize; 1]>, 1>;

    fn choose_variable(state: &mut State<Self>) -> Option<usize> {
        choose_random_variable(state)
    }

    const DEBUG: bool = false;
    const USE_BACKTRACK_STATE: bool = false;
}

impl ConfigT for RandomConfigDebug {
    type BitSet = fixed_bitset::BitSet<Vec<[usize; 1]>, 1>;

    fn choose_variable(state: &mut State<Self>) -> Option<usize> {
        choose_random_variable(state)
    }

    const DEBUG: bool = true;
    const USE_BACKTRACK_STATE: bool = false;
}

pub type Default = State<RandomConfig>;
pub type DefaultDebug = State<RandomConfigDebug>;
