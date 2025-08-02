use pror::cdcl::*;
use pror::dimacs;

pub fn main() {
    // let formula = dimacs::read_string(dimacs::SUDOKU);
    // let formula = vec![vec![1, 2], vec![-2, 3], vec![-1, -3]];
    // let formula = dimacs::read_string(dimacs::FAIL_EG);
    let formula = dimacs::read_string(dimacs::SUCC_EG);
    // let res = State::<FirstSetConfigDebug>::solve(formula);
    // let res = Default::solve(formula);
    let res = DefaultDebug::solve(formula);
    println! {"res: {:?}", res};
}
