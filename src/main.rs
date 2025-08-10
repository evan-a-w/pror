use pror::bitset::*;
use pror::cdcl::*;
use pror::dimacs;
use pror::fixed_bitset::*;
use pror::sat::*;

fn step_and_print<Config: ConfigT>(solver: &mut State<Config>, literal_override: Option<Literal>) {
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
    let res = Default::solve(formula);
    println! {"res: {:?}", res};
}

fn stepped1() {
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

    let mut solver = DefaultDebug::new_from_vec(formula);
    step_and_print(&mut solver, Some(Literal::new(1, false)));
    step_and_print(&mut solver, Some(Literal::new(2, false)));
    step_and_print(&mut solver, Some(Literal::new(2, false)));
    step_and_print(&mut solver, None);
    step_and_print(&mut solver, None);
    step_and_print(&mut solver, None);
    step_and_print(&mut solver, Some(Literal::new(5, false)));
    step_and_print(&mut solver, None);
    step_and_print(&mut solver, None);
    step_and_print(&mut solver, None);
    // let res = DefaultDebug::solve(formula);
    // println! {"res: {:?}", res};
}

fn stepped3() {
    let formula: Vec<Vec<isize>> = vec![
        vec![3, -10, -13, 1, 12, 15, 9, -5, 6, 14, 4],
        vec![-10, 14, 5, -3, -12, -6, 8, -4, 11, 9, -15, 1, -7, -13],
        vec![-4, 10, 12, -5, 8, 15, -6, -13, -7],
        vec![-13, -15, -12, -11, 14, 8, 5],
        vec![13, 3, 8, 5, 10, 12, -14, -11],
        vec![-4, -13],
        vec![14, 11],
        vec![-14, 13, -5, -6],
        vec![-5, 4, -14],
        vec![12, -6, 8, 2],
        vec![-4, 8, 6, 15, -3, -13, 9, 12, 2, 1, 11, 7, 10, -5],
        vec![-14, 9, 5, -11, -15, 1, -4, 12, 13, -2],
        vec![15, -7, -12, 6],
        vec![11, -8, -15, 13, 1, -3, 5, -12, 7, -14, -9, 10],
        vec![-11, -2, -1, -3, -12, -13, -6, 14, -5, -10, -4, -9],
        vec![-9, -10, 6, 14, -5, 11, 7, -2, 8, -4, -3],
        vec![6, 5, -14, 12, 1, -13, 10, 9, 11, 7, -8, -2, -15, 3, -4],
        vec![2, 3, -10, 8, 15, -4, -14, 1],
        vec![9, 3],
        vec![-8, 7, -4, -5, -2],
        vec![-2, -15, -14, 3, -11, -7, 1, 12],
        vec![-3, -5, 8],
        vec![-15, -4, 3, -1, 12, -10, -14, -2, 13, -6, -8],
        vec![-11, -14, -3, -9, 8, -1, -13, 7, 5],
        vec![-3],
        vec![14, -3, 15, 7, 4, -8, -13, 10, -12, 6, -5, 2, -9, -1, -11],
        vec![12, 8, -2, -6, -5, -15, 10, 7, -9],
        vec![15, 13],
        vec![9, -1, -15, -3, 2, 12, 6, 14, 5],
        vec![-1, 13, -4, 11],
        vec![14, 6, -5, 12],
        vec![13, -6, 3, 9, 7, 10, 1, -4, -15],
        vec![-3, -8],
        vec![-2, 8, -12, 14, 7],
        vec![-9, 2, -12, -11, 3],
        vec![4, -10],
        vec![11, 9, -8, 7, 1, 5, 6, -4],
        vec![7, -14, 6, 5, 15, -13, -1, -3, -11, 8],
        vec![2, 9, 3, 5, 1, -7],
        vec![9, -11, 3],
        vec![-7, 1, 9, 12, 10, 4, 11, 6, 2, -15],
        vec![9, -6],
        vec![12, 5, -6, 14, 8, 10, 13, -7, -2, -11, 15, -3, 9, 1, -4],
        vec![-10, -9, -8],
        vec![12, -15, 8, -2, 6, 3, -14, 10],
        vec![15, -9, 4, 6, -7],
        vec![4, 10, -2, 8, -9, -14, -12],
        vec![-10],
        vec![-14, -3],
        vec![1, 6, 5, -11, 12, 2, -9, 10, 4, 7],
        vec![-6, -1, 11],
        vec![-7, -10, -3, 15, 11, -14, 8],
        vec![-14, -8, -12, -15, 10, 9, 6, -13, 3, 4, 5, 7, 1, 2],
        vec![3, -12, -5, -1],
        vec![6, -9, 10, 13, -4, 1, -15, 14, 2, -7, 5, 8, 11, 12],
        vec![-10, 3],
        vec![-5, 1, -4, 11, 12, 15, 3, -13, 9, 14, -10, -7, 2, 6, 8],
        vec![3, -9, 6, 7, -5, -14, 15],
        vec![-11, -5, -1, -7, -15, 12, -8, -3],
        vec![-1, -9, -12, -2, 11, 3, -7, -5, 6, 14, 15, -13, -8],
        vec![3, -12, 6, -15, -10, -8, 1, 13, -4, -9, 14, 2],
        vec![13, 1, -3, -15, 2, 14],
        vec![6, -4, -15, 7, 8, -5, 3, -2, 1, -11],
        vec![4],
        vec![4, -2, 12, -6, 13, -15],
        vec![-1, 4, -8, 9, 13, -5, -14],
        vec![-1, -7, 8, 10, 11, 6, 3, 2],
        vec![6, 11, 3, -10, -13, -8, -14, -4],
        vec![-4, -12, 5, 13, -10, -9, 7, 1, 11, -3, 8],
        vec![-10, -2, 7, -3, 11, 1, -14, 12, 13],
        vec![7, 14, -6, -10, -8],
        vec![-5, -1, -7, -14, -11, 8],
        vec![15, -3, 8, 7, 2, 14],
        vec![-3],
        vec![-13, -11, 10, -14, 9, -5, 15, 3, -1],
        vec![4, -9, 11, 7, -3, -5, -2],
        vec![8, -6, -3, -7],
        vec![-8, 14, -5, -2, 10, -9, -11],
        vec![-10, -14, 11],
        vec![-13, -5, 11, 3, 8, 12, 15],
        vec![2, 12, -14, 8, -13, -3],
        vec![11, 2, -12, -3, -8, -14, 5, 10, 4, 15, -1],
        vec![-11, 2, 1, 8, 4, 7, -10, -5],
    ];
    let solver = DefaultDebug::solve(formula);
    println!("res: {:?}", solver);
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

fn simple() {
    let formula = vec![vec![1, 2], vec![-2, 3], vec![-1, -3]];
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

fn factor_sat_eg() {
    let formula = dimacs::read_string(dimacs::FACTOR_1234321);
    let res = Default::solve(formula);
    println! {"res: {:?}", res};
}

fn factor_unsat_eg() {
    let formula = dimacs::read_string(dimacs::FACTOR_1235321);
    let res = Default::solve(formula);
    println! {"res: {:?}", res};
}

fn subsets_100_eg() {
    let formula = dimacs::read_string(dimacs::SUBSETS_100);
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
    // stepped1();
    // stepped3();

    wikipedia();
    long();
    succ_eg();
    sudoku();
    simple();

    factor_sat_eg();
    factor_unsat_eg();

    subsets_100_eg();

    fail_eg();
}
