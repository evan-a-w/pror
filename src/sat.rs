use crate::bitset::BitSetT;
use crate::pool::Pool;
use std::collections::{BTreeMap, HashMap};
use std::collections::HashSet;

#[derive(Debug)]
pub enum SatResult {
    Sat(BTreeMap<usize, bool>),
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
        Clause {
            variables,
            negatives,
        }
    }

    pub fn can_resolve(&self, other: &Self, on_var: usize) -> bool {
        self.variables.contains(on_var)
            && other.negatives.contains(on_var)
            && !(self.negatives.contains(on_var) != other.negatives.contains(on_var))
    }

    pub fn resolve_exn(&mut self, other: &Self, on_var: usize) {
        if !self.can_resolve(other, on_var) {
            panic!("Cannot resolve clauses on variable {}", on_var);
        }

        self.variables.union_with(&other.variables);
        self.negatives.union_with(&other.negatives);
        self.variables.clear(on_var);
        self.negatives.clear(on_var);
    }

    pub fn iter_literals<'a>(&'a self) -> impl Iterator<Item = Literal> + 'a {
        self.variables
            .iter()
            .map(|var| Literal::new(var, !self.negatives.contains(var)))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Copy, Hash)]
pub struct Literal {
    value: isize,
}

impl Literal {
    pub fn new(var: usize, value: bool) -> Self {
        Literal {
            value: if value { var as isize } else { -(var as isize) },
        }
    }

    pub fn variable(&self) -> usize {
        self.value.abs() as usize
    }

    pub fn value(&self) -> bool {
        self.value > 0
    }

    pub fn negate(&self) -> Self {
        Literal { value: -self.value }
    }
}

pub struct Formula<BitSet: BitSetT> {
    pub max_var: usize,
    pub vars: HashSet<usize>,
    pub clauses: Vec<Clause<BitSet>>,
    pub literal_counts: HashMap<Literal, usize>,
}

impl<BitSet: BitSetT> Formula<BitSet> {
    pub fn new(formula: Vec<Vec<isize>>, bitset_pool: &mut Pool<BitSet>) -> Self {
        let mut max_var = 0;
        let mut vars = HashSet::new();
        let mut literal_counts = HashMap::new();
        let mut clauses = Vec::new();

        for clause in formula {
            let mut variables = bitset_pool.acquire(|| BitSet::create());
            let mut negatives = bitset_pool.acquire(|| BitSet::create());

            for lit in clause {
                if lit == 0 {
                    panic!("Can't have 0 vars");
                }
                let var = lit.abs() as usize;
                variables.set(var);
                if lit < 0 {
                    negatives.set(var);
                }

                max_var = max_var.max(var);
                vars.insert(var);
                let lit = Literal::new(var, lit > 0);
                *literal_counts.entry(lit).or_insert(0) += 1;
            }

            clauses.push(Clause {
                variables,
                negatives,
            });
        }

        Formula {
            max_var,
            vars,
            clauses,
            literal_counts,
        }
    }
}
