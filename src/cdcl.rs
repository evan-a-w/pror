use crate::bitset::{BTreeBitSet, BitSetT};
use crate::fixed_bitset;
use crate::pool::Pool;
use crate::sat::*;
use rand::prelude::*;
use rand_pcg::Pcg64;
use std::cell::RefCell;
use std::collections::BTreeMap;

pub trait ConfigT: Sized {
    type BitSet: BitSetT + Clone;

    fn choose_literal(state: &mut State<Self>) -> Option<Literal>;

    const DEBUG: bool;
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
    watched_clauses: Vec<Vec<ClauseIdx>>,
    trail: Vec<TrailEntry<Config::BitSet>>,
    unassigned_variables: Config::BitSet,
    unsatisfied_clauses: Config::BitSet,
    clauses_by_var: Vec<Config::BitSet>,
    trail_entry_idx_by_var: Vec<Option<usize>>,
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

    fn first_unit_clause(&self) -> Option<(Literal, ClauseIdx)> {
        self.unsatisfied_clauses.iter().find_map(|clause_idx| {
            let clause = &self.clauses[clause_idx];
            self.try_get_unit_literal(clause)
                .map(|literal| (literal, ClauseIdx(clause_idx)))
        })
    }

    fn clauses_mut(&mut self, literal: Literal) -> &mut Config::BitSet {
        &mut self.clauses_by_var[literal.variable()]
    }

    fn clauses(&self, literal: Literal) -> &Config::BitSet {
        &self.clauses_by_var[literal.variable()]
    }

    fn would_be_contradiction(&self, literal: Literal) -> Option<ClauseIdx> {
        self.clauses(literal)
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
        debug!(
            self.debug_writer,
            "undoing trail entry: {} at decision level {}",
            trail_entry.literal.to_string(),
            trail_entry.decision_level
        );
        let satisfied_clauses = std::mem::take(&mut trail_entry.satisfied_clauses);
        match satisfied_clauses {
            None => (),
            Some(clauses) => {
                self.unsatisfied_clauses.union_with(&clauses);
                self.bitset_pool.release(clauses);
            }
        };
        self.trail_entry_idx_by_var[trail_entry.literal.variable()] = None;
        self.unassigned_variables
            .set(trail_entry.literal.variable());
    }

    fn acquire_bitset(&mut self) -> Config::BitSet {
        let mut res = self.bitset_pool.acquire(|| Config::BitSet::create());
        res.clear_all();
        res
    }

    fn free_bitset(&mut self, bitset: Config::BitSet) {
        self.bitset_pool.release(bitset);
    }

    fn satisfy_clauses(&mut self, trail_entry: &TrailEntry<Config::BitSet>) -> Config::BitSet {
        let literal = trail_entry.literal;
        let var = literal.variable();
        let mut scratch_clause_bitset = std::mem::take(&mut self.scratch_clause_bitset).unwrap();
        scratch_clause_bitset.clear_all();
        scratch_clause_bitset.intersect(self.clauses(literal), &self.unsatisfied_clauses);
        let mut newly_set = self.acquire_bitset();
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
            self.trail_entry_idx_by_var[var].is_none(),
            "trail entry for var {} already exists: {:?}",
            var,
            self.trail_entry_idx_by_var[var]
        );
        self.trail_entry_idx_by_var[var] = Some(self.trail.len());
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

    fn only_one_at_level(&self, clause: &Clause<Config::BitSet>) -> bool {
        clause
            .iter_literals()
            .filter(|&lit| match self.trail_entry_idx_by_var[lit.variable()] {
                None => false,
                Some(idx) => {
                    let entry = &self.trail[idx];
                    entry.decision_level == self.decision_level
                }
            })
            .count()
            == 1
    }

    fn second_highest_decision_level(&self, clause: &Clause<Config::BitSet>) -> usize {
        let mut max1 = 0;
        let mut max2 = 0;
        for lit in clause.iter_literals() {
            let var = lit.variable();
            let idx = match self.trail_entry_idx_by_var[var] {
                None => continue,
                Some(idx) => idx,
            };
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

    fn learn_clause_from_failure(
        &mut self,
        failed_clause_idx: ClauseIdx,
    ) -> Clause<Config::BitSet> {
        let mut learned = self.clauses[failed_clause_idx.0].copy(&mut self.bitset_pool);
        let mut num_at_level = 0;

        for lit in learned.iter_literals() {
            let var = lit.variable();
            if let Some(idx) = self.trail_entry_idx_by_var[var] {
                let entry = &self.trail[idx];
                if entry.decision_level == self.decision_level {
                    num_at_level += 1;
                }
            }
        }

        for trail_entry in self.trail.iter().rev() {
            // if self.only_one_at_level(&learned) {
            //     break;
            // }
            if num_at_level == 1 {
                break;
            }
            if !learned.variables.contains(trail_entry.literal.variable()) {
                continue;
            }
            match trail_entry.reason {
                Reason::Decision(_) => assert!(false), // never reach this
                Reason::ClauseIdx(clause_idx) => {
                    for lit in self.clauses[clause_idx].iter_literals().filter(|lit| {
                        lit.variable() == trail_entry.literal.variable()
                            || !learned.variables.contains(lit.variable())
                    }) {
                        let var = lit.variable();
                        if let Some(idx) = self.trail_entry_idx_by_var[var] {
                            let entry = &self.trail[idx];
                            if entry.decision_level == self.decision_level {
                                if var == trail_entry.literal.variable() {
                                    num_at_level -= 1;
                                } else {
                                    num_at_level += 1;
                                }
                            }
                        }
                    }
                    learned.resolve_exn(&self.clauses[clause_idx], trail_entry.literal.variable());
                }
            }
        }
        learned
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
            Some(last_entry) if last_entry.continue_ => Some(last_entry.literal.negate()),

            Some(_) | None => None,
        }
    }

    fn backtrack(&mut self, failed_clause_idx: ClauseIdx) {
        let learned_clause = self.learn_clause_from_failure(failed_clause_idx);
        let remove_greater_than = self.second_highest_decision_level(&learned_clause);
        for lit in learned_clause.iter_literals() {
            let len = self.clauses.len();
            self.clauses_mut(lit).set(len);
        }
        self.unsatisfied_clauses.set(self.clauses.len());
        self.clauses.push(learned_clause);
        self.remove_from_trail_helper(Some(remove_greater_than));
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
                self.backtrack(ClauseIdx(failed_idx));
                StepResult::Continue
            }
        }
    }

    fn make_decision(&mut self, literal_override: Option<Literal>) -> StepResult {
        if let Some(lit) = self.next_literal.take() {
            return self.react(Action::Continue(lit, false));
        }
        match Config::choose_literal(self) {
            None => {
                let assignments = self.assignments();
                let res = SatResult::Sat(assignments);
                StepResult::Done(res)
            }
            Some(literal) => {
                self.decision_level += 1;
                let literal = literal_override.unwrap_or_else(|| literal);
                self.react(Action::Continue(literal, true))
            }
        }
    }

    pub fn step(&mut self, literal_override: Option<Literal>) -> StepResult {
        self.iterations += 1;
        if let Some(res) = self.immediate_result.take() {
            return StepResult::Done(res);
        }
        let prop_res = if self.next_literal.is_some() {
            UnitPropagationResult::NothingToPropagate
        } else {
            self.unit_propagate()
        };
        match prop_res {
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
        variables_bitset.clear_all();
        let mut clauses_by_var = vec![];

        for var in vars {
            variables_bitset.set(var);
        }

        for _ in 0..num_vars {
            let mut bs = bitset_pool.acquire(|| Config::BitSet::create());
            bs.clear_all();
            clauses_by_var.push(bs);
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
        for (idx, clause) in clauses.iter().enumerate() {
            if clause.tautology {
                unsatisfied_clauses.clear(idx);
            }
        }

        let all_variables = variables_bitset.clone();
        let unassigned_variables = variables_bitset;
        let rng = Pcg64::seed_from_u64(5);
        State {
            immediate_result,
            all_variables,
            assignments: Config::BitSet::create(),
            clauses,
            trail: Vec::with_capacity(64),
            unassigned_variables,
            unsatisfied_clauses,
            clauses_by_var,
            trail_entry_idx_by_var: vec![None; num_vars],
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

pub struct RandomConfig {}
pub struct RandomConfigDebug {}

fn choose_random_literal<T: ConfigT>(state: &mut State<T>) -> Option<Literal> {
    let len = state.unassigned_variables.count();
    if len == 0 {
        None
    } else {
        let num = state.rng.random_range(0..len);
        match state.unassigned_variables.nth(num) {
            None => panic!("unassigned_variables should have been non-empty, but was empty"),
            Some(var) => {
                let value = state.rng.random_ratio(1, 2);
                Some(Literal::new(var, value))
            }
        }
    }
}

impl ConfigT for RandomConfig {
    type BitSet = fixed_bitset::BitSet<Vec<[usize; 1]>, 1>;

    fn choose_literal(state: &mut State<Self>) -> Option<Literal> {
        choose_random_literal(state)
    }

    const DEBUG: bool = false;
}

impl ConfigT for RandomConfigDebug {
    type BitSet = fixed_bitset::BitSet<Vec<[usize; 1]>, 1>;
    // type BitSet = BTreeBitSet;

    fn choose_literal(state: &mut State<Self>) -> Option<Literal> {
        choose_random_literal(state)
    }

    const DEBUG: bool = true;
}

pub type Default = State<RandomConfig>;
pub type DefaultDebug = State<RandomConfigDebug>;
