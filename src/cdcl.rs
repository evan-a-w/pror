use crate::bitset::BitSetT;
use crate::sat::*;

enum ChoicePolicy {
    FirstUnset,
}

struct TrailEntry<BitSet: BitSetT> {
    literal: Literal,
    decision_level: usize,
    is_from_decision_point: bool,
    from_clause_idx_or_decision: usize,
    satisfied_clauses: BitSet,
    continue_: bool,
}

struct State<BitSet: BitSetT> {
    choice_policy: ChoicePolicy,
    immediate_result: Option<SatResult>,
    all_variables: BitSet,
    assignments: BitSet,
    clauses: Vec<Clause<BitSet>>,
}
