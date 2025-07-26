use pror::cdcl::*;
use pror::dimacs;

#[cfg(test)]
mod tests {
    use super::*;

    use expect_test::expect;

    use pror::cdcl::{Default};
    use pror::sat::SatResult;

    #[test]
    fn simple_satisfiable_1() {
        let formula = vec![vec![1]];
        let result = Default::solve(formula);
        let s = format!("{:?}", result);
        let expect = expect!["Sat({1: true})"];
        expect.assert_eq(&s);
    }

    #[test]
    fn simple_unsatisfiable_1() {
        let formula = vec![vec![1], vec![-1]];
        let result = Default::solve(formula);
        let s = format!("{:?}", result);
        let expect = expect!["Unsat"];
        expect.assert_eq(&s);
    }

    #[test]
    fn trivial_satisfiable_empty_formula() {
        let formula: Vec<Vec<isize>> = vec![];
        let result = Default::solve(formula);
        let s = format!("{:?}", result);
        let expect = expect!["Sat({})"];
        expect.assert_eq(&s);
    }

    #[test]
    fn trivial_unsatisfiable_due_to_empty_clause() {
        let formula = vec![vec![]];
        let result = Default::solve(formula);
        let s = format!("{:?}", result);
        let expect = expect!["Unsat"];
        expect.assert_eq(&s);
    }

    #[test]
    fn satisfiable_3_vars_multiple_clauses() {
        let formula = vec![vec![1, 2], vec![-2, 3], vec![-1, -3]];
        let result = Default::solve(formula);
        let s = format!("{:?}", result);
        let expect = expect!["Sat({1: true, 2: true, 3: false})"];
        expect.assert_eq(&s);
    }

    #[test]
    fn satisfiable_dups() {
        let formula = vec![vec![1], vec![1], vec![1]];
        let result = Default::solve(formula);
        let s = format!("{:?}", result);
        let expect = expect!["Sat({1: true})"];
        expect.assert_eq(&s);
    }

    #[test]
    fn random() {
        let formula = vec![
            vec![1, 2, 3],
            vec![-1, 2, 3],
            vec![1, -2, 3],
            vec![1, 2, -3],
        ];
        let result = Default::solve(formula);
        let s = format!("{:?}", result);
        let expect = expect!["Sat({1: true, 2: true, 3: true})"];
        expect.assert_eq(&s);
    }

    #[test]
    fn tautological_clause_ignored() {
        let formula = vec![vec![1, -1], vec![2]];
        let result = Default::solve(formula);
        let s = format!("{:?}", result);
        let expect = expect!["Sat({1: false, 2: true})"];
        expect.assert_eq(&s);
    }

    #[test]
    fn unsat_with_3_literals() {
        let formula = vec![vec![1], vec![2], vec![-1, -2], vec![-3], vec![3]];
        let result = Default::solve(formula);
        let s = format!("{:?}", result);
        let expect = expect!["Unsat"];
        expect.assert_eq(&s);
    }

    #[test]
    fn sudoku_dnf() {
        let formula = dimacs::read_string(dimacs::SUDOKU);
        let result = Default::solve(formula);
        let s = format!("{:?}", result);
        let expect = expect!["Unsat"];
        expect.assert_eq(&s);
    }

    // #[test]
    // fn fail_dnf() {
    //     let formula = dimacs::read_string(dimacs::FAIL_EG);
    //     let result = Default::solve(formula);
    //     let s = format!("{:?}", result);
    //     let expect = expect![""];
    //     expect.assert_eq(&s);
    // }

    #[test]
    fn succ_dnf() {
        let formula = dimacs::read_string(dimacs::SUCC_EG);
        let result = Default::solve(formula);
        let s = format!("{:?}", result);
        let expect = expect![""];
        expect.assert_eq(&s);
    }
}
