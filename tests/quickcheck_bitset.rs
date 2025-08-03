use itertools::Itertools;
use quickcheck::{Arbitrary, Gen, QuickCheck, TestResult};
use quickcheck_macros::*;
use rand::Rng;
use std::collections::HashSet;

use pror::bitset::*;
use pror::fixed_bitset::*;

type BS1 = BitSet<Vec<[usize; 1]>, 1>;

#[derive(Clone, Debug)]
struct Ops {
    ops: Vec<BitSetOp>,
}

#[derive(Clone, Debug)]
struct BinOps {
    ops: Vec<PairBitSetOp>,
}

#[derive(Clone, Debug)]
enum BitSetOp {
    Set(usize),
    ClearNth(usize),
    Contains(usize),
    Count,
    Nth(usize),
    FirstSet,
    FirstSetGe(usize),
    // FirstUnset,
    // FirstUnsetGe(usize),
}

#[derive(Clone, Debug)]
enum BinaryOp {
    Union,
    Intersect,
    Difference,
    IterUnion,
    IterIntersect,
    IterDifference,
    IntersectFirstSet,
    IntersectFirstSetGe(usize),
}

#[derive(Clone, Debug)]
enum PairBitSetOp {
    First(BitSetOp),
    Second(BitSetOp),
    PairOnFirst(BinaryOp),
    PairOnSecond(BinaryOp),
}

impl Arbitrary for BitSetOp {
    fn arbitrary(g: &mut Gen) -> Self {
        let op = usize::arbitrary(g) % 100;
        let bit = usize::arbitrary(g) % (1 << 16);
        match op {
            0..50 => BitSetOp::Set(bit),
            50..60 => BitSetOp::ClearNth(usize::arbitrary(g) % 3),
            60..80 => BitSetOp::Contains(bit),
            80..90 => BitSetOp::FirstSetGe(bit),
            90..92 => BitSetOp::Count,
            92..98 => BitSetOp::Nth(bit),
            98..100 => BitSetOp::FirstSet,
            _ => unreachable!(),
        }
    }
}

impl Arbitrary for BinaryOp {
    fn arbitrary(g: &mut Gen) -> Self {
        let op = usize::arbitrary(g) % 100;
        let bit = usize::arbitrary(g) % (1 << 16);
        match op {
            0..5 => BinaryOp::Union,
            5..10 => BinaryOp::Intersect,
            10..15 => BinaryOp::Difference,
            15..32 => BinaryOp::IterUnion,
            32..49 => BinaryOp::IterIntersect,
            49..56 => BinaryOp::IterDifference,
            56..75 => BinaryOp::IntersectFirstSet,
            75..100 => BinaryOp::IntersectFirstSetGe(bit),
            _ => unreachable!(),
        }
    }
}

impl Arbitrary for PairBitSetOp {
    fn arbitrary(g: &mut Gen) -> Self {
        let op = usize::arbitrary(g) % 100;
        match op {
            0..25 => PairBitSetOp::First(BitSetOp::arbitrary(g)),
            25..50 => PairBitSetOp::Second(BitSetOp::arbitrary(g)),
            50..75 => PairBitSetOp::PairOnFirst(BinaryOp::arbitrary(g)),
            75..100 => PairBitSetOp::PairOnSecond(BinaryOp::arbitrary(g)),
            _ => unreachable!(),
        }
    }
}

impl Arbitrary for Ops {
    fn arbitrary(g: &mut Gen) -> Self {
        let ops = Vec::<BitSetOp>::arbitrary(g);
        Ops { ops }
    }
}

impl Arbitrary for BinOps {
    fn arbitrary(g: &mut Gen) -> Self {
        let ops = Vec::<PairBitSetOp>::arbitrary(g);
        BinOps { ops }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum UnaryRes {
    Unit,
    Bool(bool),
    Count(usize),
    Nth(Option<usize>),
    FirstSet(Option<usize>),
    FirstUnset(Option<usize>),
}

fn apply<BitSet: BitSetT>(bs: &mut BitSet, op: &BitSetOp) -> UnaryRes {
    use UnaryRes::*;
    match op {
        BitSetOp::Set(i) => {
            bs.set(*i);
            Unit
        }
        BitSetOp::ClearNth(i) => {
            match bs.nth(*i) {
                None => (),
                Some(i) => bs.clear(i),
            }
            Unit
        }
        BitSetOp::Contains(i) => Bool(bs.contains(*i)),
        BitSetOp::Count => Count(bs.count()),
        BitSetOp::Nth(n) => Nth(bs.nth(*n)),
        BitSetOp::FirstSet => FirstSet(bs.first_set()),
        BitSetOp::FirstSetGe(x) => FirstSet(bs.first_set_ge(*x)),
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct BoundedVec<const N: usize>(Vec<usize>);

impl<const N: usize> Arbitrary for BoundedVec<N> {
    fn arbitrary(g: &mut Gen) -> Self {
        let len = usize::arbitrary(g) % N;
        let vec = (0..len).map(|_| usize::arbitrary(g) % (1 << 16)).collect();
        BoundedVec(vec)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum BinaryRes {
    List(Vec<usize>),
    Unary(UnaryRes),
}

fn apply_binop<BitSet: BitSetT>(bs1: &mut BitSet, bs2: &mut BitSet, op: &BinaryOp) -> BinaryRes {
    use BinaryRes::*;
    match op {
        BinaryOp::Union => {
            bs1.union_with(bs2);
            List(bs1.iter().collect())
        }
        BinaryOp::Intersect => {
            bs1.intersect_with(bs2);
            List(bs1.iter().collect())
        }
        BinaryOp::Difference => {
            bs1.difference_with(bs2);
            List(bs1.iter().collect())
        }
        BinaryOp::IterUnion => List(bs1.iter_union(bs2).collect()),
        BinaryOp::IterIntersect => List(bs1.iter_intersection(bs2).collect()),
        BinaryOp::IterDifference => List(bs1.iter_difference(bs2).collect()),
        BinaryOp::IntersectFirstSet => {
            let first_set = bs1.intersect_first_set(bs2);
            Unary(UnaryRes::FirstSet(first_set))
        }
        BinaryOp::IntersectFirstSetGe(x) => {
            let first_set = bs1.intersect_first_set_ge(bs2, *x);
            Unary(UnaryRes::FirstSet(first_set))
        }
    }
}

fn apply2<BitSet: BitSetT>(bs1: &mut BitSet, bs2: &mut BitSet, op: &PairBitSetOp) -> BinaryRes {
    use BinaryRes::*;
    match op {
        PairBitSetOp::First(op) => Unary(apply(bs1, op)),
        PairBitSetOp::Second(op) => Unary(apply(bs2, op)),
        PairBitSetOp::PairOnFirst(binop) => apply_binop(bs1, bs2, binop),
        PairBitSetOp::PairOnSecond(binop) => apply_binop(bs2, bs1, binop),
    }
}

#[quickcheck]
fn qc_prop_bitset_matches_naive(initial_state: BoundedVec<1024>, ops: Ops) -> TestResult {
    let mut b = BS1::create();
    let mut naive = BTreeBitSet::create();
    initial_state.0.iter().for_each(|&i| {
        b.set(i);
        naive.set(i);
    });

    for op in &ops.ops {
        let res = apply(&mut b, op);
        let res_naive = apply(&mut naive, op);
        if res != res_naive {
            println!(
                "Failed on op: {:?}\ngood: {:?} ({:?})\nnaive: {:?} ({:?})",
                op,
                res,
                b.iter().collect::<Vec<usize>>(),
                res_naive,
                naive.iter().collect::<Vec<usize>>()
            );
            return TestResult::failed();
        }
    }

    TestResult::passed()
}

#[quickcheck]
fn qc_prop_bitset_matches_naive2(
    initial_state_a: BoundedVec<1024>,
    initial_state_b: BoundedVec<1024>,
    ops: BinOps,
) -> TestResult {
    let mut a = BS1::create();
    let mut b = BS1::create();
    let mut naive_a = BTreeBitSet::create();
    let mut naive_b = BTreeBitSet::create();

    initial_state_a.0.iter().for_each(|&i| {
        a.set(i);
        naive_a.set(i)
    });
    initial_state_b.0.iter().for_each(|&i| {
        b.set(i);
        naive_b.set(i)
    });

    for op in &ops.ops {
        let res = apply2(&mut a, &mut b, op);
        let res_naive = apply2(&mut naive_a, &mut naive_b, op);
        let la = a.iter().collect::<Vec<usize>>();
        let lb = b.iter().collect::<Vec<usize>>();

        let la_naive = naive_a.iter().collect::<Vec<usize>>();
        let lb_naive = naive_b.iter().collect::<Vec<usize>>();
        if res != res_naive || la != la_naive || lb != lb_naive {
            println!(
                "Failed on op: {:?}\ngood: {:?} ({:?}; {:?})\nnaive: {:?} ({:?}; {:?})",
                op, res, la, lb, res_naive, la_naive, lb_naive
            );
            return TestResult::failed();
        }
    }

    TestResult::passed()
}

#[quickcheck]
fn qc_intersect_first_set_ge(
    initial_state_a: BoundedVec<1024>,
    initial_state_b: BoundedVec<1024>,
    i: usize,
) -> TestResult {
    let mut a = BS1::create();
    let mut b = BS1::create();
    let mut naive_a = BTreeBitSet::create();
    let mut naive_b = BTreeBitSet::create();

    initial_state_a.0.iter().for_each(|&i| {
        a.set(i);
        naive_a.set(i)
    });
    initial_state_b.0.iter().for_each(|&i| {
        b.set(i);
        naive_b.set(i)
    });

    let max_a = initial_state_a.0.iter().max().copied().unwrap_or(0);
    let max_b = initial_state_b.0.iter().max().copied().unwrap_or(0);
    let ge = if max_a.max(max_b) == 0 {
        0
    } else {
        i % max_a.max(max_b)
    };

    let res = a.intersect_first_set_ge(&b, ge);
    let naive_res = naive_a.intersect_first_set_ge(&naive_b, ge);
    if res != naive_res {
        println!(
            "Failed on intersect_first_set_ge with ge: {}\n\
             good: {:?} ({:?})\n\
             naive: {:?} ({:?})",
            ge,
            res,
            a.iter().collect::<Vec<usize>>(),
            naive_res,
            naive_a.iter().collect::<Vec<usize>>()
        );
        return TestResult::failed();
    }

    TestResult::passed()
}

#[quickcheck]
fn qc_intersect_first_set(
    initial_state_a: BoundedVec<1024>,
    initial_state_b: BoundedVec<1024>,
) -> TestResult {
    let mut a = BS1::create();
    let mut b = BS1::create();
    let mut naive_a = BTreeBitSet::create();
    let mut naive_b = BTreeBitSet::create();

    initial_state_a.0.iter().for_each(|&i| {
        a.set(i);
        naive_a.set(i)
    });
    initial_state_b.0.iter().for_each(|&i| {
        b.set(i);
        naive_b.set(i)
    });

    let res = a.intersect_first_set(&b);
    let naive_res = naive_a.intersect_first_set(&naive_b);
    if res != naive_res {
        println!(
            "Failed on intersect_first_set\n\
             good: {:?} ({:?})\n\
             naive: {:?} ({:?})",
            res,
            a.iter().collect::<Vec<usize>>(),
            naive_res,
            naive_a.iter().collect::<Vec<usize>>()
        );
        return TestResult::failed();
    }

    TestResult::passed()
}
