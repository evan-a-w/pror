use std::collections::HashMap;
use crate::bitset::BitSetT;

pub enum SatResult {
    Sat(HashMap<usize, bool>),
    Unsat,
}

pub enum StepResult {
    Done(SatResult),
    Continue,
}


pub struct Clause<BitSet: BitSetT> {
    pub variables: BitSet,
    pub negatives: BitSet,
}

impl<BitSet: BitSetT> Clause<BitSet> {
    pub fn create(variables: BitSet, negatives: BitSet) -> Self {
        Clause { variables, negatives }
    }
}

pub struct Literal {
    value: isize,
}

impl Literal {
    pub fn new(var: u32, value: bool) -> Self {
        Literal {
            value: if value { var as isize } else { -(var as isize) },
        }
    }
}
