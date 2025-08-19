use crate::bitset::{BTreeBitSet, BitSetT};
use crate::fixed_bitset;
use crate::luby::Luby;
use crate::pool::Pool;
use crate::sat::*;
use crate::tombstone::*;
use itertools::Itertools;
use ordered_float::OrderedFloat;
use quickcheck::Gen;
use rand::prelude::*;
use rand_pcg::Pcg64;
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};

pub trait ConfigT: Sized {
    type BitSet: BitSetT + Clone;

    fn choose_literal(state: &mut State<Self>) -> Option<Literal>;

    const DEBUG: bool;
    const CHECK_RESULTS: bool; // check the assignments actually match
}

#[macro_export]
macro_rules! debug {
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

struct TrailEntry {
    literal: Literal,
    decision_level: usize,
    reason: Reason,
}

struct TfPair<T> {
    pub first: T,
    pub second: T,
}

impl<T> std::ops::Index<bool> for TfPair<T> {
    type Output = T;

    fn index(&self, index: bool) -> &Self::Output {
        if index {
            &self.first
        } else {
            &self.second
        }
    }
}

impl<T> std::ops::IndexMut<bool> for TfPair<T> {
    fn index_mut(&mut self, index: bool) -> &mut T {
        if index {
            &mut self.first
        } else {
            &mut self.second
        }
    }
}

pub struct State<Config: ConfigT> {
    luby: Luby,
    conflicts: u64,
    cla_inc: f64,
    cla_decay_factor: f64,
    cla_activity_rescale: f64,
    vsids_inc: f64,
    vsids_decay_factor: f64,
    vsids_activity_rescale: f64,
    score_for_literal: Vec<TfPair<f64>>,
    literal_by_score: BTreeSet<(OrderedFloat<f64>, Literal)>,
    simplify_clauses_every: usize,
    all_variables: Config::BitSet,
    assignments: Config::BitSet,
    clauses_first_tombstone: Option<usize>,
    clauses: Vec<TombStone<Clause<Config::BitSet>>>,
    clause_sorting_buckets: Vec<ClauseIdx>,
    watched_clauses: Vec<TfPair<BTreeMap<ClauseIdx, Generation>>>,
    ready_for_unit_prop: Config::BitSet,
    trail: Vec<TrailEntry>,
    unassigned_variables: Config::BitSet,
    num_initial_clauses: usize,
    clauses_by_var: Vec<TfPair<Config::BitSet>>,
    trail_entry_idx_by_var: Vec<Option<usize>>,
    decision_level: usize,
    bitset_pool: Pool<Config::BitSet>,
    iterations: usize,
    rng: Pcg64,
    debug_writer: Option<RefCell<Box<dyn std::fmt::Write>>>,
    instantly_unsat: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
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
    Continue(Literal),
    Contradiction(usize),
}

impl<Config: ConfigT> State<Config> {
    fn watched_clauses(&self, literal: Literal) -> &BTreeMap<ClauseIdx, Generation> {
        &self.watched_clauses[literal.variable()][literal.value()]
    }
    fn watched_clauses_mut(&mut self, literal: Literal) -> &mut BTreeMap<ClauseIdx, Generation> {
        &mut self.watched_clauses[literal.variable()][literal.value()]
    }

    fn push_clause(&mut self, clause: Clause<Config::BitSet>) -> usize {
        match self.clauses_first_tombstone {
            None => {
                self.clauses.push(TombStone::new(0, clause));
                self.clauses.len() - 1
            }
            Some(idx) => {
                let gen = self.clauses[idx].generation().clone();
                self.clauses_first_tombstone = self.clauses[idx].tombstone_idx_exn();
                self.clauses[idx] = TombStone::new(gen + 1, clause);
                idx
            }
        }
    }

    fn delete_clause(&mut self, idx: usize) {
        let mut next_variable = 0;
        loop {
            let clause = self.clauses[idx].value_exn();
            match clause.variables.first_set_ge(next_variable + 1) {
                None => break,
                Some(variable) => {
                    next_variable = variable;
                    self.clauses_by_var[variable][!clause.negatives.contains(variable)].clear(idx);
                }
            }
        }
        let mut rep_variables = Config::BitSet::create();
        let mut rep_negatives = Config::BitSet::create();
        std::mem::swap(
            &mut rep_variables,
            &mut self.clauses[idx].value_mut().unwrap().variables,
        );
        std::mem::swap(
            &mut rep_negatives,
            &mut self.clauses[idx].value_mut().unwrap().negatives,
        );
        self.bitset_pool.release(rep_variables);
        self.bitset_pool.release(rep_negatives);
        self.clauses[idx] = TombStone::TombStone(
            self.clauses[idx].generation().clone() + 1,
            self.clauses_first_tombstone.clone(),
        );
        self.clauses_first_tombstone = Some(idx);
    }

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

    fn clauses_mut(&mut self, literal: Literal) -> &mut Config::BitSet {
        &mut self.clauses_by_var[literal.variable()][literal.value()]
    }

    fn clauses(&self, literal: Literal) -> &Config::BitSet {
        &self.clauses_by_var[literal.variable()][literal.value()]
    }

    fn undo_entry(&mut self, trail_entry: &mut TrailEntry) {
        debug!(
            self.debug_writer,
            "undoing trail entry: {} at decision level {}",
            trail_entry.literal.to_string(),
            trail_entry.decision_level
        );
        let literal = trail_entry.literal;
        self.literal_by_score.insert((
            OrderedFloat(self.score_for_literal[literal.variable()][literal.value()]),
            literal.clone(),
        ));
        self.literal_by_score.insert((
            OrderedFloat(self.score_for_literal[literal.variable()][!literal.value()]),
            literal.negate(),
        ));
        self.trail_entry_idx_by_var[trail_entry.literal.variable()] = None;
        self.unassigned_variables
            .set(trail_entry.literal.variable());
        match trail_entry.reason {
            Reason::Decision(_) => (),
            Reason::ClauseIdx(clause_idx) => {
                self.clauses[clause_idx].value_mut().unwrap().num_units -= 1
            }
        };
    }

    fn acquire_bitset(&mut self) -> Config::BitSet {
        let mut res = self.bitset_pool.acquire(|| Config::BitSet::create());
        res.clear_all();
        res
    }

    fn free_bitset(&mut self, bitset: Config::BitSet) {
        self.bitset_pool.release(bitset);
    }

    fn is_satisfied(&self, clause: &Clause<Config::BitSet>) -> bool {
        clause.iter_literals().any(|lit| {
            !self.unassigned_variables.contains(lit.variable())
                && self.assignments.contains(lit.variable()) == lit.value()
        })
    }

    fn remove_watched_clause_due_to_generation_mismatch(
        &mut self,
        literal: Literal,
        clause_idx: ClauseIdx,
    ) -> bool {
        let ClauseIdx(idx) = clause_idx;
        let expected = self.watched_clauses(literal).get(&clause_idx).unwrap();
        if self.clauses[idx].generation() == expected {
            return false;
        }
        self.watched_clauses_mut(literal).remove(&clause_idx);
        true
    }

    fn update_watched_clauses(&mut self, set_literal: Literal) -> Option<ClauseIdx> {
        debug!(
            self.debug_writer,
            "updating watched clauses for literal {}",
            set_literal.to_string()
        );
        let literal = set_literal.negate();
        let mut next = self
            .watched_clauses(literal)
            .range(ClauseIdx(0)..)
            .next()
            .clone()
            .map(|(x, y)| (x.clone(), y.clone()));
        while let Some((ClauseIdx(clause_idx), generation)) = next {
            next = self
                .watched_clauses(literal)
                .range(ClauseIdx(clause_idx + 1)..)
                .next()
                .clone()
                .map(|(x, y)| (x.clone(), y.clone()));

            if self.remove_watched_clause_due_to_generation_mismatch(literal, ClauseIdx(clause_idx))
            {
                continue;
            }

            if self.is_satisfied(&self.clauses[clause_idx].value().unwrap()) {
                continue;
            }

            let replace = self.clauses[clause_idx]
                .value()
                .unwrap()
                .iter_literals()
                .filter(|&lit| {
                    !self
                        .watched_clauses(lit)
                        .contains_key(&ClauseIdx(clause_idx))
                        && self.unassigned_variables.contains(lit.variable())
                })
                .next();
            match replace {
                None => match self.try_get_unit_literal(&self.clauses[clause_idx].value().unwrap())
                {
                    None => return Some(ClauseIdx(clause_idx)),
                    Some(unit_literal) => {
                        debug!(
                            self.debug_writer,
                            "found unit literal ({}) while updating watched clauses for literal {} in clause ({:?})",
                            unit_literal.to_string(),
                            literal.to_string(),
                            self.clause_string(ClauseIdx(clause_idx)),
                        );
                        self.ready_for_unit_prop.set(clause_idx);
                    }
                },
                Some(to_replace) => {
                    debug!(
                        self.debug_writer,
                        "replacing watched literal {} with {} in clause ({:?})",
                        literal.to_string(),
                        to_replace.to_string(),
                        self.clause_string(ClauseIdx(clause_idx))
                    );
                    let gen = self
                        .watched_clauses_mut(literal)
                        .remove(&ClauseIdx(clause_idx))
                        .unwrap();
                    self.watched_clauses_mut(to_replace)
                        .insert(ClauseIdx(clause_idx), gen);
                }
            }
        }
        None
    }

    fn add_to_trail(&mut self, trail_entry: TrailEntry) -> Option<ClauseIdx> {
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
        match trail_entry.reason {
            Reason::Decision(_) => (),
            Reason::ClauseIdx(clause_idx) => {
                self.clauses[clause_idx].value_mut().unwrap().num_units += 1;
            }
        };
        self.literal_by_score.remove(&(
            OrderedFloat(self.score_for_literal[var][literal.value()]),
            literal.clone(),
        ));
        self.literal_by_score.remove(&(
            OrderedFloat(self.score_for_literal[var][!literal.value()]),
            literal.negate(),
        ));
        self.trail_entry_idx_by_var[var] = Some(self.trail.len());
        self.unassigned_variables.clear(var);
        self.trail.push(trail_entry);
        self.update_watched_clauses(literal)
    }

    fn clause_string(&self, clause_idx: ClauseIdx) -> String {
        self.clauses[clause_idx.0].value_exn().to_string()
    }

    fn with_unit_clause(&mut self, literal: Literal, clause_idx: ClauseIdx) -> Option<ClauseIdx> {
        debug!(
            self.debug_writer,
            "found unit clause: {:?} in clause ({:?}) unit clauses rn: {}",
            literal,
            self.clause_string(clause_idx),
            self.ready_for_unit_prop
                .iter()
                .map(|idx| self.clause_string(ClauseIdx(idx)))
                .collect::<Vec<_>>()
                .join("; ")
        );
        let decision_level = self.decision_level;
        let trail_entry = TrailEntry {
            literal,
            decision_level,
            reason: Reason::ClauseIdx(clause_idx.0),
        };
        self.add_to_trail(trail_entry)
    }

    fn unit_propagate(&mut self) -> UnitPropagationResult {
        let mut num_props = 0;
        while let Some(clause_idx) = self.ready_for_unit_prop.pop_first_set() {
            match self.clauses[clause_idx]
                .value()
                .and_then(|x| self.try_get_unit_literal(x))
            {
                None => continue,
                Some(literal) => {
                    if let Some(clause_idx) = self.with_unit_clause(literal, ClauseIdx(clause_idx))
                    {
                        return UnitPropagationResult::Contradiction(clause_idx);
                    };
                    num_props += 1;
                }
            }
        }
        if num_props == 0 {
            UnitPropagationResult::NothingToPropagate
        } else {
            UnitPropagationResult::FinishedUnitPropagation
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

    fn rescale_clause_activities(&mut self) {
        for clause in self.clauses.iter_mut().filter_map(|x| x.value_mut()) {
            clause.score /= self.cla_activity_rescale;
        }
        self.cla_inc /= self.cla_activity_rescale;
    }

    fn add_clause_activity(&mut self, clause_idx: usize) -> bool {
        self.clauses[clause_idx].value_mut_exn().score += self.cla_inc;
        // should rescale
        self.clauses[clause_idx].value_mut_exn().score > self.cla_activity_rescale
    }

    fn add_clause_activity_and_maybe_rescale(&mut self, clause_idx: usize) {
        if self.add_clause_activity(clause_idx) {
            self.rescale_clause_activities();
        }
    }

    fn decay_clause_activities(&mut self) {
        self.cla_inc /= self.cla_decay_factor;
    }

    fn rescale_vsids(&mut self) {
        let (all_variables, score_for_literal, literal_by_score, rescale) = (
            &self.all_variables,
            &mut self.score_for_literal,
            &mut self.literal_by_score,
            &self.vsids_activity_rescale,
        );

        for literal in all_variables.iter().flat_map(|variable| {
            [Literal::new(variable, false), Literal::new(variable, true)].into_iter()
        }) {
            let score = &mut score_for_literal[literal.variable()][literal.value()];
            let rem = literal_by_score.remove(&(OrderedFloat(*score), literal));
            *score /= rescale;
            if rem {
                literal_by_score.insert((OrderedFloat(*score), literal.clone()));
            }
        }

        self.vsids_inc /= self.vsids_activity_rescale;
    }

    fn add_vsids_activity(&mut self, literal: Literal) {
        let score = &mut self.score_for_literal[literal.variable()][literal.value()];
        let rem = self
            .literal_by_score
            .remove(&(OrderedFloat(*score), literal));
        *score += self.vsids_inc;
        if rem {
            self.literal_by_score
                .insert((OrderedFloat(*score), literal.clone()));
        }
        if *score > self.vsids_activity_rescale {
            self.rescale_vsids()
        }
    }

    fn decay_vsids_activities(&mut self) {
        self.vsids_inc /= self.vsids_decay_factor;
    }

    fn learn_clause_from_failure(
        &mut self,
        failed_clause_idx: ClauseIdx,
    ) -> Clause<Config::BitSet> {
        let mut learned = self.clauses[failed_clause_idx.0]
            .value_exn()
            .copy(&mut self.bitset_pool);
        learned.from_conflict = true;
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

        let mut rescale = false;
        for trail_entry_idx in (0..self.trail.len()).rev() {
            // if self.only_one_at_level(&learned) {
            //     break;
            // }
            if num_at_level == 1 {
                break;
            }
            let reason = self.trail[trail_entry_idx].reason.clone();
            if !learned
                .variables
                .contains(self.trail[trail_entry_idx].literal.variable())
            {
                continue;
            }
            self.add_vsids_activity(self.trail[trail_entry_idx].literal);
            match reason {
                Reason::Decision(_) => assert!(false, "found decision walking back from conflict"),
                Reason::ClauseIdx(clause_idx) => {
                    rescale = rescale || self.add_clause_activity(clause_idx);
                    let trail_entry = &self.trail[trail_entry_idx];
                    for lit in self.clauses[clause_idx]
                        .value_exn()
                        .iter_literals()
                        .filter(|lit| {
                            lit.variable() == trail_entry.literal.variable()
                                || !learned.variables.contains(lit.variable())
                        })
                    {
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
                    learned.resolve_exn(
                        &self.clauses[clause_idx].value_exn(),
                        trail_entry.literal.variable(),
                    );
                }
            }
        }
        if rescale {
            self.rescale_clause_activities()
        }
        learned
    }

    fn restart(&mut self) {
        debug!(self.debug_writer, "Restarting");
        self.ready_for_unit_prop.clear_all();
        while let Some(mut trail_entry) = self.trail.pop() {
            self.undo_entry(&mut trail_entry);
        }
        for (clause_idx, clause) in self
            .clauses
            .iter()
            .enumerate()
            .filter_map(|(i, x)| x.value().map(|v| (i, v)))
        {
            if let Some(_) = self.try_get_unit_literal(clause) {
                debug!(
                    self.debug_writer,
                    "Found unit after restart in clause {}",
                    self.clause_string(ClauseIdx(clause_idx))
                );
                self.ready_for_unit_prop.set(clause_idx);
            }
        }
    }

    fn remove_from_trail_helper(&mut self, remove_greater_than: Option<usize>) {
        let mut trail_entry: Option<TrailEntry> = None;
        loop {
            let finished = self.trail.is_empty()
                || match remove_greater_than {
                    None => trail_entry.as_ref().is_some(),
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
    }

    fn backtrack(&mut self, failed_clause_idx: ClauseIdx) {
        let learned_clause = self.learn_clause_from_failure(failed_clause_idx);
        learned_clause
            .iter_literals()
            .for_each(|lit| self.add_vsids_activity(lit));
        let remove_greater_than = self.second_highest_decision_level(&learned_clause);
        for lit in learned_clause.iter_literals() {
            let len = self.clauses.len();
            self.clauses_mut(lit).set(len);
        }
        self.decay_vsids_activities();
        self.remove_from_trail_helper(Some(remove_greater_than));
        let clause_idx = self.push_clause(learned_clause);
        self.ready_for_unit_prop.clear_all();
        self.update_watch_literals_for_new_clause(clause_idx);
    }

    fn react(&mut self, action: Action) -> StepResult {
        debug!(
            self.debug_writer,
            "reacting to action: {:?} at decision level {}", action, self.decision_level
        );
        match action {
            Action::Unsat => StepResult::Done(SatResult::Unsat),
            Action::FinishedUnitPropagation => StepResult::Continue,
            Action::Continue(literal) => {
                let trail_entry = TrailEntry {
                    literal,
                    decision_level: self.decision_level,
                    reason: Reason::Decision(literal),
                };
                self.add_to_trail(trail_entry);
                StepResult::Continue
            }
            Action::Contradiction(_) if self.decision_level == 0 => {
                StepResult::Done(SatResult::Unsat)
            }
            Action::Contradiction(failed_idx) => {
                self.conflicts += 1;
                self.backtrack(ClauseIdx(failed_idx));
                if self.conflicts >= self.luby.value() {
                    self.conflicts = 0;
                    self.restart();
                }
                StepResult::Continue
            }
        }
    }

    fn make_decision(&mut self, literal_override: Option<Literal>) -> StepResult {
        match literal_override.or_else(|| Config::choose_literal(self)) {
            None => {
                let assignments = self.assignments();
                let res = SatResult::Sat(assignments);
                StepResult::Done(res)
            }
            Some(literal) => {
                self.decision_level += 1;
                self.react(Action::Continue(literal))
            }
        }
    }

    fn can_trim_clause(&self, clause: &Clause<Config::BitSet>) -> bool {
        clause.num_units == 0
            && clause
                .iter_literals()
                .filter_map(|x| self.trail_entry_idx_by_var[x.variable()])
                .map(|x| self.trail[x].decision_level)
                .unique()
                .collect::<Vec<_>>()
                .len()
                >= 3
            && clause.variables.count() >= 3
    }

    fn simplify_clauses(&mut self) {
        let mut sorting_buckets = vec![];
        std::mem::swap(&mut sorting_buckets, &mut self.clause_sorting_buckets);
        sorting_buckets.clear();
        for (idx, clause) in self
            .clauses
            .iter()
            .enumerate()
            .skip(self.num_initial_clauses)
            .filter_map(|(i, x)| x.value().map(|x| (i, x)))
            .filter(|(_, x)| x.from_conflict && x.num_units == 0 && self.can_trim_clause(x))
        {
            sorting_buckets.push(ClauseIdx(idx));
        }
        sorting_buckets.sort_by(|ClauseIdx(a), ClauseIdx(b)| {
            f64::total_cmp(
                &self.clauses[*a].value_exn().score,
                &self.clauses[*b].value_exn().score,
            )
        });
        for x in &sorting_buckets {
            debug!(
                self.debug_writer,
                "Clause {x:?} {}",
                self.clause_string(x.clone())
            );
        }
        let num_to_drop = sorting_buckets.len() / 2;
        // not bothered to sort out ownership so just iterating over i
        for ClauseIdx(clause_idx) in sorting_buckets.iter().take(num_to_drop) {
            debug!(
                self.debug_writer,
                "Deleting clause {clause_idx} (score {}), {}",
                self.clauses[*clause_idx].value_exn().score,
                self.clause_string(ClauseIdx(*clause_idx))
            );
            self.delete_clause(*clause_idx);
        }
        std::mem::swap(&mut sorting_buckets, &mut self.clause_sorting_buckets);
    }

    pub fn step(&mut self, literal_override: Option<Literal>) -> StepResult {
        self.iterations += 1;
        if self.iterations % self.simplify_clauses_every == 0 {
            debug!(
                self.debug_writer,
                "simplifying clauses at iteration {}, num clauses {}, level {}",
                self.iterations,
                self.clauses
                    .iter()
                    .filter_map(|x| x.value())
                    .collect::<Vec<_>>()
                    .len(),
                self.decision_level
            );
            self.simplify_clauses();
            self.decay_clause_activities();
        };
        if self.instantly_unsat {
            return StepResult::Done(SatResult::Unsat);
        }
        match self.unit_propagate() {
            UnitPropagationResult::NothingToPropagate => self.make_decision(literal_override),
            UnitPropagationResult::FinishedUnitPropagation => StepResult::Continue,
            UnitPropagationResult::Contradiction(ClauseIdx(idx)) => {
                self.react(Action::Contradiction(idx))
            }
        }
    }

    fn run_inner(&mut self) -> SatResult {
        loop {
            match self.step(None) {
                StepResult::Done(SatResult::Unsat) => return SatResult::Unsat,
                StepResult::Done(SatResult::Sat(res)) => {
                    if Config::CHECK_RESULTS {
                        assert!(satisfies(&self.clauses, &res));
                    }
                    return SatResult::Sat(res);
                }
                StepResult::Continue => continue,
            }
        }
    }

    pub fn run(&mut self) -> SatResult {
        self.restart();
        self.run_inner()
    }

    fn stabilize_assumption(&mut self) -> Option<SatResult> {
        match self.unit_propagate() {
            UnitPropagationResult::Contradiction(ClauseIdx(idx)) => Some(SatResult::Unsat),
            UnitPropagationResult::NothingToPropagate
            | UnitPropagationResult::FinishedUnitPropagation => None,
        }
    }

    pub fn run_with_assumptions(&mut self, assumptions: &[isize]) -> SatResult {
        self.restart();

        match self.stabilize_assumption() {
            Some(res) => return res,
            None => (),
        }
        for &lit_val in assumptions {
            let var = lit_val.abs() as usize;
            let value = lit_val > 0;
            let lit = Literal::new(var, value);
            if !self.unassigned_variables.contains(var) {
                if self.assignments.contains(var) != value {
                    return SatResult::Unsat;
                } else {
                    continue;
                }
            }
            match self.make_decision(Some(lit)) {
                StepResult::Continue => (),
                StepResult::Done(res) => return res,
            }
            match self.stabilize_assumption() {
                Some(res) => return res,
                None => (),
            }
        }
        self.run_inner()
    }

    fn update_watch_literals_for_new_clause_helper(
        debug_writer: &Option<RefCell<Box<dyn std::fmt::Write>>>,
        clause: &Clause<Config::BitSet>,
        clause_idx: usize,
        generation: Generation,
        watched_clauses: &mut Vec<TfPair<BTreeMap<ClauseIdx, Generation>>>,
        ready_for_unit_prop: &mut Config::BitSet,
        unassigned_variables: &Config::BitSet,
    ) {
        let mut unassigned_lits = clause
            .variables
            .iter_intersection(unassigned_variables)
            .map(|var| Literal::new(var, !clause.negatives.contains(var)));
        let mut assigned_lits = clause
            .variables
            .iter_difference(unassigned_variables)
            .map(|var| Literal::new(var, !clause.negatives.contains(var)));
        match (
            unassigned_lits.next(),
            unassigned_lits.next(),
            assigned_lits.next(),
            assigned_lits.next(),
        ) {
            (None, None, None, None) => (),
            (None, None, Some(lit), None) => {
                watched_clauses[lit.variable()][lit.value()]
                    .insert(ClauseIdx(clause_idx), generation);
            }
            (None, None, Some(lit1), Some(lit2)) => {
                watched_clauses[lit1.variable()][lit1.value()]
                    .insert(ClauseIdx(clause_idx), generation);
                watched_clauses[lit2.variable()][lit2.value()]
                    .insert(ClauseIdx(clause_idx), generation);
            }
            (Some(lit), None, Some(lit2), _) => {
                watched_clauses[lit.variable()][lit.value()]
                    .insert(ClauseIdx(clause_idx), generation);
                watched_clauses[lit2.variable()][lit2.value()]
                    .insert(ClauseIdx(clause_idx), generation);
                debug!(
                    debug_writer,
                    "adding watched literal {} for unit clause ({:?})",
                    lit.to_string(),
                    clause.to_string()
                );
                ready_for_unit_prop.set(clause_idx);
            }
            (Some(lit), None, None, None) => {
                watched_clauses[lit.variable()][lit.value()]
                    .insert(ClauseIdx(clause_idx), generation);
                debug!(
                    debug_writer,
                    "adding watched literal {} for unit clause ({:?})",
                    lit.to_string(),
                    clause.to_string()
                );
                ready_for_unit_prop.set(clause_idx);
            }
            (Some(a), Some(b), _, _) => {
                debug!(
                    debug_writer,
                    "adding watched literals {} and {} for clause ({:?})",
                    a.to_string(),
                    b.to_string(),
                    clause.to_string()
                );
                watched_clauses[a.variable()][a.value()].insert(ClauseIdx(clause_idx), generation);
                watched_clauses[b.variable()][b.value()].insert(ClauseIdx(clause_idx), generation);
            }
            _ => assert!(false),
        };
    }

    fn update_watch_literals_for_new_clause(&mut self, clause_idx: usize) {
        Self::update_watch_literals_for_new_clause_helper(
            &self.debug_writer,
            &self.clauses[clause_idx].value_exn(),
            clause_idx,
            self.clauses[clause_idx].generation().clone(),
            &mut self.watched_clauses,
            &mut self.ready_for_unit_prop,
            &self.unassigned_variables,
        )
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
        let clauses = clauses
            .into_iter()
            .map(|x| TombStone::new(0, x))
            .collect::<Vec<_>>();
        let num_vars = max_var + 1;
        let mut variables_bitset = Config::BitSet::create();
        variables_bitset.clear_all();
        let mut clauses_by_var = vec![];
        let mut watched_clauses = vec![];
        let mut ready_for_unit_prop = Config::BitSet::create();

        for var in vars {
            variables_bitset.set(var);
        }

        for _ in 0..num_vars {
            let mut bs = TfPair {
                first: bitset_pool.acquire(|| Config::BitSet::create()),
                second: bitset_pool.acquire(|| Config::BitSet::create()),
            };
            bs.first.clear_all();
            bs.second.clear_all();
            clauses_by_var.push(bs);
            watched_clauses.push(TfPair {
                first: BTreeMap::new(),
                second: BTreeMap::new(),
            });
        }

        let mut instantly_unsat = false;

        let debug_writer = match debug_writer {
            None => None,
            Some(w) => {
                let b: Box<dyn std::fmt::Write> = Box::new(w);
                Some(RefCell::new(b))
            }
        };

        for (idx, clause) in clauses.iter().filter_map(|x| x.value()).enumerate() {
            // all things aren't tombstones rn so enumerate after filter map is ifne
            if clause.variables.is_empty() {
                instantly_unsat = true;
            }
            clause.iter_literals().for_each(|lit| {
                clauses_by_var[lit.variable()][lit.value()].set(idx);
            });
            Self::update_watch_literals_for_new_clause_helper(
                &debug_writer,
                clause,
                idx,
                0,
                &mut watched_clauses,
                &mut ready_for_unit_prop,
                &variables_bitset,
            );
        }

        let num_initial_clauses = clauses.len();
        let all_variables = variables_bitset.clone();
        let unassigned_variables = variables_bitset;
        let rng = Pcg64::seed_from_u64(5);

        let score_for_literal = (0..num_vars)
            .map(|variable| {
                let first = clauses_by_var[variable][true].count() as f64;
                let second = clauses_by_var[variable][false].count() as f64;
                TfPair { first, second }
            })
            .collect::<Vec<_>>();

        let literal_by_score = all_variables
            .iter()
            .flat_map(|i| {
                let score = &score_for_literal[i];
                [
                    (OrderedFloat(score[true]), Literal::new(i, true)),
                    (OrderedFloat(score[false]), Literal::new(i, false)),
                ]
                .into_iter()
            })
            .collect::<BTreeSet<_>>();

        State {
            luby: Luby::new(32),
            conflicts: 0,
            score_for_literal,
            literal_by_score,
            cla_decay_factor: 0.75,
            cla_activity_rescale: 1e20,
            cla_inc: 1.0,
            vsids_decay_factor: 0.95,
            vsids_activity_rescale: 1e20,
            vsids_inc: 1.0,
            clauses_first_tombstone: None,
            clause_sorting_buckets: vec![],
            simplify_clauses_every: 2500,
            ready_for_unit_prop,
            all_variables,
            assignments: Config::BitSet::create(),
            clauses,
            num_initial_clauses,
            trail: Vec::with_capacity(64),
            unassigned_variables,
            watched_clauses,
            clauses_by_var,
            trail_entry_idx_by_var: vec![None; num_vars],
            decision_level: 0,
            bitset_pool,
            iterations: 0,
            rng,
            debug_writer,
            instantly_unsat,
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

    pub fn create(formula: Vec<Vec<isize>>) -> Self {
        Self::new_from_vec(formula)
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

    pub fn solve_with_debug_writer_and_assumptions<Writer: std::fmt::Write + 'static>(
        formula: Vec<Vec<isize>>,
        assumptions: &[isize],
        debug_writer: Option<Writer>,
    ) -> SatResult {
        let mut state = Self::new_from_vec_with_debug_writer(formula, debug_writer);
        state.run_with_assumptions(assumptions)
    }

    pub fn solve_with_assumptions(formula: Vec<Vec<isize>>, assumptions: &[isize]) -> SatResult {
        Self::solve_with_debug_writer_and_assumptions::<String>(formula, assumptions, None)
    }

    pub fn solve_with_debug_writer<Writer: std::fmt::Write + 'static>(
        formula: Vec<Vec<isize>>,
        debug_writer: Option<Writer>,
    ) -> SatResult {
        let mut state = Self::new_from_vec_with_debug_writer(formula, debug_writer);
        state.run_inner()
    }

    pub fn solve(formula: Vec<Vec<isize>>) -> SatResult {
        Self::solve_with_debug_writer::<String>(formula, None)
    }
}

pub struct RandomConfig {}
pub struct RandomConfigDebug {}

pub struct VsidsConfig {}
pub struct VsidsConfigDebug {}

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

fn choose_vsids_literal<T: ConfigT>(state: &mut State<T>) -> Option<Literal> {
    state
        .literal_by_score
        .last()
        .map(|(_, literal)| literal.clone())
}

impl ConfigT for RandomConfig {
    type BitSet = fixed_bitset::BitSet;

    fn choose_literal(state: &mut State<Self>) -> Option<Literal> {
        choose_random_literal(state)
    }

    const DEBUG: bool = false;
    const CHECK_RESULTS: bool = false;
}

impl ConfigT for RandomConfigDebug {
    type BitSet = fixed_bitset::BitSet;

    fn choose_literal(state: &mut State<Self>) -> Option<Literal> {
        choose_random_literal(state)
    }

    const DEBUG: bool = true;
    const CHECK_RESULTS: bool = true;
}

impl ConfigT for VsidsConfig {
    type BitSet = fixed_bitset::BitSet;

    fn choose_literal(state: &mut State<Self>) -> Option<Literal> {
        choose_vsids_literal(state)
    }

    const DEBUG: bool = false;
    const CHECK_RESULTS: bool = false;
}

impl ConfigT for VsidsConfigDebug {
    type BitSet = fixed_bitset::BitSet;

    fn choose_literal(state: &mut State<Self>) -> Option<Literal> {
        choose_vsids_literal(state)
    }

    const DEBUG: bool = true;
    const CHECK_RESULTS: bool = true;
}

// pub type Default = State<RandomConfig>;
pub type Default = State<VsidsConfig>;
pub type DefaultDebug = State<VsidsConfigDebug>;
