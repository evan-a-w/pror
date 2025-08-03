use pror::bitset::*;
use pror::cdcl::*;
use pror::dimacs;
use pror::fixed_bitset::*;
use pror::sat::*;

fn step_and_print(solver: &mut Default, literal_override: Option<Literal>) {
    let result = solver.step(literal_override);
    println!("\n{:?}", result);
}

fn long() {
    let formula = vec![
        vec![1, 2, 3],
        vec![1, 2, -3],
        vec![-2, 4],
        vec![1, -2, -4],
        vec![-1, 5, 6],
        vec![-1, 5, -6],
        vec![-5, -6],
        vec![-1, -5, 6],
    ];
    let mut solver = Default::new_from_vec(formula);
    step_and_print(&mut solver, Some(Literal::new(1, false)));
    step_and_print(&mut solver, Some(Literal::new(2, false)));
    step_and_print(&mut solver, Some(Literal::new(2, false)));
}

fn wikipedia() {
    let formula = vec![
        vec![1, 4],
        vec![1, -3, -8],
        vec![1, 8, 12],
        vec![2, 11],
        vec![-3, -7, 9],
        vec![-7, 8, -9],
        vec![7, 8, -10],
        vec![7, 10, -12],
    ];
    let mut solver = Default::new_from_vec(formula);
    step_and_print(&mut solver, Some(Literal::new(1, false)));
    step_and_print(&mut solver, None);
    step_and_print(&mut solver, Some(Literal::new(3, true)));
    step_and_print(&mut solver, None);
    step_and_print(&mut solver, Some(Literal::new(2, false)));
    step_and_print(&mut solver, None);
    step_and_print(&mut solver, Some(Literal::new(7, true)));
    for _ in 1..12 {
        step_and_print(&mut solver, None);
    }
}

fn sudoku() {
    let formula = dimacs::read_string(dimacs::SUDOKU);
    let res = Default::solve(formula);
    println! {"res: {:?}", res};
}

fn succ_eg() {
    let formula = dimacs::read_string(dimacs::SUCC_EG);
    let res = Default::solve(formula);
    println! {"res: {:?}", res};
}

fn fail_eg() {
    let formula = dimacs::read_string(dimacs::FAIL_EG);
    let res = Default::solve(formula);
    println! {"res: {:?}", res};
}

fn useless_set_thing() {
    let mut a = DefaultBitSet::create();
    let mut b = DefaultBitSet::create();
    a.set(1);
    a.set(3);
    a.set(323213123);
    b.set(10);
    b.set(101024);
    a.iter_union(&b).for_each(|x| {
        println!("x: {}", x);
    });
}

pub fn main() {
    wikipedia();
    long();
    fail_eg();
    succ_eg();
    sudoku();
}
