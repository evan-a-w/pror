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

pub fn main() {
    // long()
    let formula = dimacs::read_string(dimacs::SUDOKU);
    // let formula = vec![vec![1, 2], vec![-2, 3], vec![-1, -3]];
    // let formula = dimacs::read_string(dimacs::FAIL_EG);
    // let formula = dimacs::read_string(dimacs::SUCC_EG);
    // let res = Default::solve(formula);
    let res = DefaultDebug::solve(formula);
    println! {"res: {:?}", res};

}
