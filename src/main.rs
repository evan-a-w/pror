use pror::cdcl::*;
use pror::dimacs;
use pror::sat::*;

fn step_and_print(solver: &mut DefaultDebug, literal_override: Option<Literal>) {
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
    let mut solver = DefaultDebug::new_from_vec(formula);
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
    let mut solver = DefaultDebug::new_from_vec(formula);
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

pub fn main() {
    // wikipedia();
    // long()
    let formula = dimacs::read_string(dimacs::SUDOKU);
    // let formula = vec![vec![1, 2], vec![-2, 3], vec![-1, -3]];
    // let formula = dimacs::read_string(dimacs::FAIL_EG);
    // let formula = dimacs::read_string(dimacs::SUCC_EG);
    // let res = Default::solve(formula);
    // let res = DefaultDebug::solve(formula);
    let res = State::<FirstSetConfigDebug>::solve(formula);
    println! {"res: {:?}", res};
}
