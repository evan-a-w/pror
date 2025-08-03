use pror::cdcl::*;
use pror::dimacs;
use pror::sat::*;
use pror::shared_string_writer::SharedStringWriter;

#[cfg(test)]
mod tests {
    use super::*;

    use expect_test::expect;

    use pror::cdcl::Default;
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
        let expect = expect!["Sat({1: true, 2: false, 3: false})"];
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
        let expect = expect!["Sat({1: true, 2: false, 3: true})"];
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
    fn stepped1() {
        use std::fmt::Write;
        fn step_and_print<Writer: std::fmt::Write>(
            mut s: Writer,
            solver: &mut DefaultDebug,
            literal_override: Option<Literal>,
        ) {
            let result = solver.step(literal_override);
            writeln!(s, "\n{:?}", result);
        }
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
        let mut writer = SharedStringWriter::new();
        let mut solver =
            DefaultDebug::new_from_vec_with_debug_writer(formula, Some(writer.clone()));
        step_and_print(&mut writer, &mut solver, Some(Literal::new(1, false)));
        step_and_print(&mut writer, &mut solver, Some(Literal::new(2, false)));
        step_and_print(&mut writer, &mut solver, Some(Literal::new(2, false)));
        step_and_print(&mut writer, &mut solver, None);
        step_and_print(&mut writer, &mut solver, None);
        step_and_print(&mut writer, &mut solver, None);
        step_and_print(&mut writer, &mut solver, Some(Literal::new(5, false)));
        step_and_print(&mut writer, &mut solver, None);
        step_and_print(&mut writer, &mut solver, None);
        let expect = expect![[r#"
            reacting to action: Continue(Literal { value: -1 }, true) at decision level 1
            adding to trail at decision level 1: -1
            satisfy_clauses: clauses satisfied by literal -1: (-1 5 6), (-1 5 -6), (-1 -5 6)

            Continue
            reacting to action: Continue(Literal { value: -2 }, true) at decision level 2
            adding to trail at decision level 2: -2
            satisfy_clauses: clauses satisfied by literal -2: (-2 4), (1 -2 -4)

            Continue
            found unit clause: Literal { value: 3 } in clause ("(1 2 3)")
            would be contradiction with clause "(1 2 -3)" for literal 3
            adding to trail at decision level 2: 3
            satisfy_clauses: clauses satisfied by literal 3: (1 2 3)
            reacting to action: Contradiction(1) at decision level 2
            undoing trail entry: 3 at decision level 2
            undoing trail entry: -2 at decision level 2

            Continue
            found unit clause: Literal { value: 2 } in clause ("(1 2)")
            adding to trail at decision level 1: 2
            satisfy_clauses: clauses satisfied by literal 2: (1 2 3), (1 2 -3), (-2 4), (1 -2 -4), (1 2)
            found unit clause: Literal { value: 4 } in clause ("(-2 4)")
            would be contradiction with clause "(1 -2 -4)" for literal 4
            adding to trail at decision level 1: 4
            satisfy_clauses: clauses satisfied by literal 4: (1 2 3), (-2 4)
            reacting to action: Contradiction(3) at decision level 1
            undoing trail entry: 4 at decision level 1
            undoing trail entry: 2 at decision level 1
            undoing trail entry: -1 at decision level 1

            Continue
            found unit clause: Literal { value: 1 } in clause ("(1)")
            adding to trail at decision level 0: 1
            satisfy_clauses: clauses satisfied by literal 1: (1 2 3), (1 2 -3), (1 -2 -4), (-1 5 6), (-1 5 -6), (-1 -5 6), (1 2), (1)

            Continue
            reacting to action: Continue(Literal { value: 3 }, true) at decision level 1
            adding to trail at decision level 1: 3
            satisfy_clauses: clauses satisfied by literal 3: (1 2 3), (1 2 -3), (-2 4), (1 -2 -4), (1 2)

            Continue
            reacting to action: Continue(Literal { value: -5 }, true) at decision level 2
            adding to trail at decision level 2: -5
            satisfy_clauses: clauses satisfied by literal -5: (1 2 3), (-2 4), (-5 -6), (-1 -5 6)

            Continue
            found unit clause: Literal { value: 6 } in clause ("(-1 5 6)")
            would be contradiction with clause "(-1 5 -6)" for literal 6
            adding to trail at decision level 2: 6
            satisfy_clauses: clauses satisfied by literal 6: (-1 5 6)
            reacting to action: Contradiction(5) at decision level 2
            undoing trail entry: 6 at decision level 2
            undoing trail entry: -5 at decision level 2
            undoing trail entry: 3 at decision level 1

            Continue
            found unit clause: Literal { value: 2 } in clause ("(1 2)")
            adding to trail at decision level 0: 2
            satisfy_clauses: clauses satisfied by literal 2: (1 2 3), (1 2 -3), (-2 4), (1 -2 -4), (1 2)
            found unit clause: Literal { value: 4 } in clause ("(-2 4)")
            would be contradiction with clause "(1 -2 -4)" for literal 4
            adding to trail at decision level 0: 4
            satisfy_clauses: clauses satisfied by literal 4: (1 2 3), (-2 4), (-5 -6), (-1 -5 6)
            reacting to action: Contradiction(3) at decision level 0

            Done(Unsat)
        "#]];
        expect.assert_eq(writer.borrow().as_ref());
    }

    #[test]
    fn stepped2() {
        use std::fmt::Write;
        let formula: Vec<Vec<isize>> = vec![
            vec![3, -5, 6],
            vec![-2, -5, -3, 6, -4],
            vec![-5, 1, 4, -6],
            vec![3, -4, 6, 1, 2, 5],
            vec![-3, 4, -2, 6, -1, -5],
            vec![3, -2, -6, 4],
            vec![3, 2, -1],
            vec![-6, -4, 5, -3],
            vec![-3, 2, 5, 6, -1, -4],
            vec![4, -2, -3, 5],
            vec![3, -2, -1, -5, -6, -4],
            vec![-2, -6],
            vec![-1, -2, 4, 5],
            vec![2, -4, 1, 3, -5, -6],
        ];
        let mut writer = SharedStringWriter::new();
        let res = DefaultDebug::solve_with_debug_writer(formula, Some(writer.clone()));
        writeln!(writer, "{:?}", res);
        let expect = expect![[r#"
            reacting to action: Continue(Literal { value: -3 }, true) at decision level 1
            adding to trail at decision level 1: -3
            satisfy_clauses: clauses satisfied by literal -3: (-2 -3 -4 -5 6), (-1 -2 -3 4 -5 6), (-3 -4 5 -6), (-1 2 -3 -4 5 6), (-2 -3 4 5)
            reacting to action: Continue(Literal { value: -6 }, true) at decision level 2
            adding to trail at decision level 2: -6
            satisfy_clauses: clauses satisfied by literal -6: (1 4 -5 -6), (-2 3 4 -6), (-1 -2 3 -4 -5 -6), (-2 -6), (1 2 3 -4 -5 -6)
            found unit clause: Literal { value: -5 } in clause ("(3 -5 6)")
            adding to trail at decision level 2: -5
            satisfy_clauses: clauses satisfied by literal -5: (3 -5 6)
            reacting to action: Continue(Literal { value: 1 }, true) at decision level 3
            adding to trail at decision level 3: 1
            satisfy_clauses: clauses satisfied by literal 1: (1 2 3 -4 5 6)
            found unit clause: Literal { value: 2 } in clause ("(-1 2 3)")
            adding to trail at decision level 3: 2
            satisfy_clauses: clauses satisfied by literal 2: (-1 2 3)
            found unit clause: Literal { value: 4 } in clause ("(-1 -2 4 5)")
            adding to trail at decision level 3: 4
            satisfy_clauses: clauses satisfied by literal 4: (-1 -2 4 5)
            Sat({1: true, 2: true, 3: false, 4: true, 5: false, 6: false})
        "#]];
        expect.assert_eq(writer.borrow().as_ref());
    }

    #[test]
    fn stepped3() {
        use std::fmt::Write;
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
        let mut writer = SharedStringWriter::new();
        let res = DefaultDebug::solve_with_debug_writer(formula, Some(writer.clone()));
        writeln!(writer, "{:?}", res);
        let expect = expect![[r#"
            found unit clause: Literal { value: -3 } in clause ("(-3)")
            adding to trail at decision level 0: -3
            satisfy_clauses: clauses satisfied by literal -3: (1 -3 -4 5 -6 -7 8 9 -10 11 -12 -13 14 -15), (1 2 -3 -4 -5 6 7 8 9 10 11 12 -13 15), (1 -3 5 7 -8 -9 10 11 -12 13 -14 -15), (-1 -2 -3 -4 -5 -6 -9 -10 -11 -12 -13 14), (-2 -3 -4 -5 6 7 8 -9 -10 11 14), (-3 -5 8), (-1 -3 5 7 8 -9 -11 -13 -14), (-3), (-1 2 -3 4 -5 6 7 -8 -9 10 -11 -12 -13 14 15), (-1 2 -3 5 6 9 12 14 -15), (-3 -8), (-1 -3 5 6 7 8 -11 -13 -14 15), (1 -2 -3 -4 5 -6 -7 8 9 10 -11 12 13 14 15), (-3 -14), (-3 -7 8 -10 11 -14 15), (-1 -3 -5 -7 -8 -11 12 -15), (1 2 -3 13 14 -15), (1 -3 -4 5 7 8 -9 -10 11 -12 13), (1 -2 -3 7 -10 11 12 13 -14), (2 -3 7 8 14 15), (-3), (-2 -3 4 -5 7 -9 11), (-3 -6 -7 8), (2 -3 8 12 -13 -14), (-1 2 -3 4 5 -8 10 11 -12 -14 15)
            found unit clause: Literal { value: 9 } in clause ("(3 9)")
            adding to trail at decision level 0: 9
            satisfy_clauses: clauses satisfied by literal 9: (1 3 4 -5 6 9 -10 12 -13 14 15), (1 -2 -4 5 9 -11 12 13 -14 -15), (1 -2 3 -4 5 6 7 -8 9 10 11 12 -13 -14 -15), (3 9), (1 3 -4 -6 7 9 10 13 -15), (1 -4 5 6 7 -8 9 11), (1 2 3 5 -7 9), (3 9 -11), (1 2 4 6 -7 9 10 11 12 -15), (-6 9), (1 2 3 4 5 6 7 -8 9 10 -12 -13 -14 -15), (1 2 3 -4 -5 6 -7 8 9 -10 11 12 -13 14 15), (-1 4 -5 -8 9 13 -14), (-1 3 -5 9 10 -11 -13 -14 15)
            found unit clause: Literal { value: -10 } in clause ("(-10)")
            adding to trail at decision level 0: -10
            satisfy_clauses: clauses satisfied by literal -10: (1 2 3 -4 8 -10 -14 15), (-1 -2 3 -4 -6 -8 -10 12 13 -14 -15), (4 -10), (-8 -9 -10), (-10), (3 -10), (1 2 3 -4 6 -8 -9 -10 -12 13 14 -15), (3 -4 6 -8 -10 11 -13 -14), (-6 7 -8 -10 14), (-10 11 -14), (1 2 4 -5 7 8 -10 -11)
            found unit clause: Literal { value: 4 } in clause ("(4)")
            adding to trail at decision level 0: 4
            satisfy_clauses: clauses satisfied by literal 4: (4 -5 -14), (4 6 -7 -9 15), (-2 4 8 -9 10 -12 -14), (1 2 4 5 6 7 -9 10 -11 12), (4), (-2 4 -6 12 13 -15)
            found unit clause: Literal { value: -13 } in clause ("(-4 -13)")
            adding to trail at decision level 0: -13
            satisfy_clauses: clauses satisfied by literal -13: (-4 -5 -6 -7 8 10 12 -13 15), (5 8 -11 -12 -13 14 -15), (-4 -13), (-1 -2 3 -5 6 -7 -8 -9 11 -12 -13 14 15), (3 -5 8 11 12 -13 15)
            found unit clause: Literal { value: 15 } in clause ("(13 15)")
            adding to trail at decision level 0: 15
            satisfy_clauses: clauses satisfied by literal 15: (6 -7 -12 15), (13 15), (3 -5 6 7 -9 -14 15)
            reacting to action: Continue(Literal { value: -7 }, true) at decision level 1
            adding to trail at decision level 1: -7
            satisfy_clauses: clauses satisfied by literal -7: (1 -2 3 -7 -11 12 -14 -15), (1 2 -4 5 6 -7 8 -9 10 11 12 13 14 -15), (-1 2 3 6 -7 8 10 11), (-1 -5 -7 8 -11 -14)
            reacting to action: Continue(Literal { value: -14 }, true) at decision level 2
            adding to trail at decision level 2: -14
            satisfy_clauses: clauses satisfied by literal -14: (3 5 8 10 -11 12 13 -14), (-5 -6 13 -14), (-2 3 6 8 10 12 -14 -15)
            found unit clause: Literal { value: 11 } in clause ("(11 14)")
            adding to trail at decision level 2: 11
            satisfy_clauses: clauses satisfied by literal 11: (11 14), (-1 -4 11 13), (-1 -6 11)
            reacting to action: Continue(Literal { value: 2 }, true) at decision level 3
            adding to trail at decision level 3: 2
            satisfy_clauses: clauses satisfied by literal 2: (2 -6 8 12), (2 3 -9 -11 -12)
            reacting to action: Continue(Literal { value: 6 }, true) at decision level 4
            adding to trail at decision level 4: 6
            satisfy_clauses: clauses satisfied by literal 6: (-5 6 12 14), (1 -2 3 -4 -5 6 7 8 -11 -15)
            reacting to action: Continue(Literal { value: -5 }, true) at decision level 5
            adding to trail at decision level 5: -5
            satisfy_clauses: clauses satisfied by literal -5: (-2 -4 -5 7 -8), (-2 -5 -6 7 8 -9 10 12 -15), (-1 3 -5 -12), (-2 -5 -8 -9 10 -11 14)
            reacting to action: Continue(Literal { value: 8 }, true) at decision level 6
            adding to trail at decision level 6: 8
            satisfy_clauses: clauses satisfied by literal 8: (-2 7 8 -12 14)
            reacting to action: Continue(Literal { value: 12 }, true) at decision level 7
            adding to trail at decision level 7: 12
            satisfy_clauses: clauses satisfied by literal 12: 
            reacting to action: Continue(Literal { value: 1 }, true) at decision level 8
            adding to trail at decision level 8: 1
            satisfy_clauses: clauses satisfied by literal 1: 
            Sat({1: true, 2: true, 3: false, 4: true, 5: false, 6: true, 7: false, 8: true, 9: true, 10: false, 11: true, 12: true, 13: false, 14: false, 15: true})
        "#]];
        expect.assert_eq(writer.borrow().as_ref());
    }

    #[test]
    fn stepped4() {
        use std::fmt::Write;
        let formula: Vec<Vec<isize>> = vec![
            vec![-1, -4, -2, -8, 6, 5, -7, -3],
            vec![1, -7],
            vec![-6, 7, 8, 3, -1, 5, 2, -4],
            vec![-3, -4, -5, 2, -6],
            vec![6, 3, -2, -7],
            vec![6, 8, -4, 7, -2, -5],
            vec![-6, 1, -3, -5, 2, -8, -4],
            vec![7],
            vec![-5, -8, -1, -7],
            vec![-8, -4],
            vec![4, 3],
            vec![-2, -8],
            vec![3, 6, 2, -1, -4],
            vec![2, 5, -1, -4, 3, -8, -6, -7],
            vec![2, 7, 6, 1],
            vec![-1, 3, 6],
            vec![-2, -6, -4, -8, 5, -1, 3, -7],
            vec![-2, 3, 8, -5, -1],
            vec![-5, -1, 6, 3, -2, -4],
            vec![4],
            vec![-4, 2, -5, 6, -8, 7],
            vec![-8, 1],
            vec![4],
            vec![6, -8, 2, 3, 4, 7, -5],
            vec![4, -3, 6, -8],
            vec![6, -4, 2, -3, 7],
            vec![-4],
            vec![1],
            vec![-6, 3, 1, -5],
            vec![5, 7, -8, 4, 6],
            vec![-7, 5, 4, -3, -8, -6, -1, 2],
            vec![-4, -8, 7, 6, 3, 2, 5, 1],
            vec![5, 2, -8, -3, -4, -6, 7],
            vec![2, -7, -1, -6, -8, 3],
            vec![3, -1, -2, -4, -6],
            vec![6, -4, 2, 5],
            vec![-3, 6],
            vec![-4, -1, -2, 3, -8],
            vec![2, -7, -6, -3, -8, -4],
            vec![3, -5, -8, -4, 7, 2, -1, 6],
            vec![-1, 5, 4, 8, -6],
            vec![-5, 4, -7],
            vec![2, 3, -4, -7, 1, 6, -8],
            vec![-1],
            vec![2, 3, -8, 7, 4, 5, -6, 1],
            vec![-7],
            vec![2, -8, -6, -4, 7],
            vec![-2],
            vec![-3, -8, -6],
            vec![3, 4, -8, -6, 2, -1, 5],
            vec![5, 6],
            vec![6, 7],
            vec![-7, 6, -5],
            vec![3, 6, -1, -8, 5],
            vec![-4, 5, 8, 2, 7],
            vec![4, 5, 3, -1],
            vec![1, -2, 5, -3, -8, -6, -7],
            vec![-2, 4, -3, -1, 5],
            vec![-3, 2, -8, -6, -1, 5, -4],
            vec![7, -8, -2, 4, 3, -1],
            vec![3, -2],
            vec![-4, 3, 5, -8, -1, -6],
            vec![1, 2],
            vec![3, 1, 5, 7, 8, 2, -4, 6],
            vec![-4, 2, 1, 6, -8, 5, -7],
            vec![-2, -4, -3, 6, 1, 8, -5],
            vec![-1, -2, 7, -8, 6, -3, -5, -4],
            vec![-7, 2, 4, -1, -8, -6],
            vec![5, 4],
            vec![-3, -8, 2],
            vec![-5, 2, -8],
            vec![-6, -5, 2, -1],
            vec![3, -4, -7, -2, -8, -1],
            vec![-3, -8, -7],
            vec![5, -6, 2, -8, -3],
            vec![-6, -1, -5, 3, -2, -7, -4],
            vec![3, -4, 1, -2, -8, 6, -7, -5],
            vec![8, -5, -7, -2],
            vec![1, -7, 4],
            vec![8, -6, 2],
            vec![-4, 5, -2, -6, 1, -3, 7, -8],
            vec![-4],
            vec![7, 8, 5, 6, 2],
            vec![-4, 1],
            vec![3, 7, -8, -4, -6, 2],
            vec![-1, 7, 2, -6, -4, 3, -8, -5],
            vec![-8, 1, 7, 5, -2, 4, 6, 3],
            vec![-7, -6, -5],
            vec![-1, 6, 2, 4, -8, 7, 5, 3],
            vec![-4, 3, -6, -2, -7, -8, -5],
            vec![4, 8],
            vec![1, -8, 7, 4, -6, -3, 2, -5],
            vec![-8],
            vec![4, -5, 6],
            vec![1, -2],
            vec![7, -6, 4, -8, -5],
            vec![-3, -7, -5],
            vec![-2, -6, 7, 8, 1, -3],
            vec![7, 2, 4],
            vec![-1, -7, 2, -5, -8],
            vec![-5, -2, -1, 8, -6],
            vec![8, 1, -5, -6, 2, 3, 7],
            vec![6, 8, 5],
            vec![-8, -6, -2, 1, -4, 7, 5],
            vec![6],
            vec![2, -7, 5],
            vec![1, -6, 7, 5, -4, 2],
            vec![-4, -1, -2, -5, -3, -7, -6, 8],
            vec![2, 7, 1, -8, 5],
            vec![7, -8, 2, 6, 5, -3, -4, -1],
            vec![-4, 2, 6, 7, 1, 8, -3],
            vec![5],
            vec![-8, 1, 5, -2, 4, 7],
            vec![-4, 2],
            vec![7, -1],
            vec![-5, -4, 2, 8, -7, -6, 3, 1],
            vec![7, -8],
            vec![-8],
            vec![3, 1, 8],
            vec![-1, 6, 7, 2, -3, -8],
            vec![2, -4],
            vec![5, 3, 8, -7],
            vec![-3, 5, -7, 1, 2, -6, -4],
            vec![4, -5, 7, 3, 1, -8, -6],
            vec![-3, -1, 4, 7, -6, -2, -8, 5],
            vec![-2, -4, -3, -8],
            vec![6, 3],
            vec![-1, 8, -3, -4, -2, -6, -7],
            vec![5, 8, 2, -3, 1, 7, -4, -6],
            vec![4, -5, -1, -8, 3],
            vec![3, -2, -8, 7, -1],
        ];
        let mut writer = SharedStringWriter::new();
        let res = DefaultDebug::solve_with_debug_writer(formula, Some(writer.clone()));
        writeln!(writer, "{:?}", res);
        let expect = expect![[r#"
            found unit clause: Literal { value: 7 } in clause ("(7)")
            would be contradiction with clause "(-7)" for literal 7
            adding to trail at decision level 0: 7
            satisfy_clauses: clauses satisfied by literal 7: (-1 2 3 -4 5 -6 7 8), (-2 -4 -5 6 7 8), (7), (1 2 6 7), (2 -4 -5 6 7 -8), (2 3 4 -5 6 7 -8), (2 -3 -4 6 7), (4 5 6 7 -8), (1 2 3 -4 5 6 7 -8), (2 -3 -4 5 -6 7 -8), (-1 2 3 -4 -5 6 7 -8), (1 2 3 4 5 -6 7 -8), (2 -4 -6 7 -8), (6 7), (2 -4 5 7 8), (-1 -2 3 4 7 -8), (1 2 3 -4 5 6 7 8), (-1 -2 -3 -4 -5 6 7 -8), (1 -2 -3 -4 5 -6 7 -8), (2 5 6 7 8), (2 3 -4 -6 7 -8), (-1 2 3 -4 -5 -6 7 -8), (1 -2 3 4 5 6 7 -8), (-1 2 3 4 5 6 7 -8), (1 2 -3 4 -5 -6 7 -8), (4 -5 -6 7 -8), (1 -2 -3 -6 7 8), (2 4 7), (1 2 3 -5 -6 7 8), (1 -2 -4 5 -6 7 -8), (1 2 -4 5 -6 7), (1 2 5 7 -8), (-1 2 -3 -4 5 6 7 -8), (1 2 -3 -4 6 7 8), (1 -2 4 5 7 -8), (-1 7), (7 -8), (-1 2 -3 6 7 -8), (1 3 4 -5 -6 7 -8), (-1 -2 -3 4 5 -6 7 -8), (1 2 -3 -4 5 -6 7 8), (-1 -2 3 7 -8)
            reacting to action: Contradiction(45) at decision level 0
            Unsat
        "#]];
        expect.assert_eq(writer.borrow().as_ref());
    }

    // #[test]
    // fn sudoku_dnf() {
    //     let formula = dimacs::read_string(dimacs::SUDOKU);
    //     let result = Default::solve(formula);
    //     let s = format!("{:?}", result);
    //     let expect = expect!["Sat({1: false, 2: false, 3: false, 4: false, 5: true, 6: false, 7: false, 8: false, 9: false, 10: true, 11: true, 12: true, 13: true, 14: true, 15: true, 16: true, 17: true, 18: true, 19: true, 20: true, 21: true, 22: true, 23: true, 24: true, 25: true, 26: true, 27: true, 28: true, 29: true, 30: true, 31: true, 32: true, 33: true, 34: true, 35: true, 36: true, 37: true, 38: true, 39: true, 40: true, 41: true, 42: true, 43: true, 44: true, 45: true, 46: true, 47: true, 48: true, 49: true, 50: true, 51: true, 52: true, 53: true, 54: true, 55: true, 56: true, 57: true, 58: true, 59: true, 60: true, 61: true, 62: true, 63: true, 64: true, 65: true, 66: true, 67: true, 68: true, 69: true, 70: true, 71: true, 72: true, 73: true, 74: true, 75: true, 76: true, 77: true, 78: true, 79: true, 80: true, 81: true, 82: true, 83: true, 84: true, 85: true, 86: true, 87: true, 88: true, 89: true, 90: true, 91: true, 92: true, 93: true, 94: true, 95: true, 96: true, 97: true, 98: true, 99: true, 100: true, 101: true, 102: true, 103: true, 104: true, 105: true, 106: true, 107: true, 108: true, 109: true, 110: true, 111: true, 112: true, 113: true, 114: true, 115: true, 116: true, 117: true, 118: true, 119: true, 120: true, 121: true, 122: true, 123: true, 124: true, 125: true, 126: true, 127: true, 128: true, 129: true, 130: true, 131: true, 132: true, 133: true, 134: true, 135: true, 136: true, 137: true, 138: true, 139: true, 140: true, 141: true, 142: true, 143: true, 144: true, 145: true, 146: true, 147: true, 148: true, 149: true, 150: true, 151: true, 152: true, 153: true, 154: true, 155: true, 156: true, 157: true, 158: true, 159: true, 160: true, 161: true, 162: true, 163: true, 164: true, 165: true, 166: true, 167: true, 168: true, 169: true, 170: true, 171: true, 172: true, 173: true, 174: true, 175: true, 176: true, 177: true, 178: true, 179: true, 180: true, 181: true, 182: true, 183: true, 184: true, 185: true, 186: true, 187: true, 188: true, 189: true, 190: true, 191: true, 192: true, 193: true, 194: true, 195: true, 196: true, 197: true, 198: true, 199: true, 200: true, 201: true, 202: true, 203: true, 204: true, 205: true, 206: true, 207: true, 208: true, 209: true, 210: true, 211: true, 212: true, 213: true, 214: true, 215: true, 216: true, 217: true, 218: true, 219: true, 220: true, 221: true, 222: true, 223: true, 224: true, 225: true, 226: true, 227: true, 228: true, 229: true, 230: true, 231: true, 232: true, 233: true, 234: true, 235: true, 236: true, 237: true, 238: true, 239: true, 240: true, 241: true, 242: true, 243: true, 244: true, 245: true, 246: true, 247: true, 248: true, 249: true, 250: true, 251: true, 252: true, 253: true, 254: true, 255: true, 256: true, 257: true, 258: true, 259: true, 260: true, 261: true, 262: true, 263: true, 264: true, 265: true, 266: true, 267: true, 268: true, 269: true, 270: true, 271: true, 272: true, 273: true, 274: true, 275: true, 276: true, 277: true, 278: true, 279: true, 280: true, 281: true, 282: true, 283: true, 284: true, 285: true, 286: true, 287: true, 288: true, 289: true, 290: true, 291: true, 292: true, 293: true, 294: true, 295: true, 296: true, 297: true, 298: true, 299: true, 300: true, 301: true, 302: true, 303: true, 304: true, 305: true, 306: true, 307: true, 308: true, 309: true, 310: true, 311: true, 312: true, 313: true, 314: true, 315: true, 316: true, 317: true, 318: true, 319: true, 320: true, 321: true, 322: true, 323: true, 324: true, 325: true, 326: true, 327: true, 328: true, 329: true, 330: true, 331: true, 332: true, 333: true, 334: true, 335: true, 336: true, 337: true, 338: true, 339: true, 340: true, 341: true, 342: true, 343: true, 344: true, 345: true, 346: true, 347: true, 348: true, 349: true, 350: true, 351: true, 352: true, 353: true, 354: true, 355: true, 356: true, 357: true, 358: true, 359: true, 360: true, 361: true, 362: true, 363: true, 364: true, 365: true, 366: true, 367: true, 368: true, 369: true, 370: true, 371: true, 372: true, 373: true, 374: true, 375: true, 376: true, 377: true, 378: true, 379: true, 380: true, 381: true, 382: true, 383: true, 384: true, 385: true, 386: true, 387: true, 388: true, 389: true, 390: true, 391: true, 392: true, 393: true, 394: true, 395: true, 396: true, 397: true, 398: true, 399: true, 400: true, 401: true, 402: true, 403: true, 404: true, 405: true, 406: true, 407: true, 408: true, 409: true, 410: true, 411: true, 412: true, 413: true, 414: true, 415: true, 416: true, 417: true, 418: true, 419: true, 420: true, 421: true, 422: true, 423: true, 424: true, 425: true, 426: true, 427: true, 428: true, 429: true, 430: true, 431: true, 432: true, 433: true, 434: true, 435: true, 436: true, 437: true, 438: true, 439: true, 440: true, 441: true, 442: true, 443: true, 444: true, 445: true, 446: true, 447: true, 448: true, 449: true, 450: true, 451: true, 452: true, 453: true, 454: true, 455: true, 456: true, 457: true, 458: true, 459: true, 460: true, 461: true, 462: true, 463: true, 464: true, 465: true, 466: true, 467: true, 468: true, 469: true, 470: true, 471: true, 472: true, 473: true, 474: true, 475: true, 476: true, 477: true, 478: true, 479: true, 480: true, 481: true, 482: true, 483: true, 484: true, 485: true, 486: true, 487: true, 488: true, 489: true, 490: true, 491: true, 492: true, 493: true, 494: true, 495: true, 496: true, 497: true, 498: true, 499: true, 500: true, 501: true, 502: true, 503: true, 504: true, 505: true, 506: true, 507: true, 508: true, 509: true, 510: true, 511: true, 512: true, 513: true, 514: true, 515: true, 516: true, 517: true, 518: true, 519: true, 520: true, 521: true, 522: true, 523: true, 524: true, 525: true, 526: true, 527: true, 528: true, 529: true, 530: true, 531: true, 532: true, 533: true, 534: true, 535: true, 536: true, 537: true, 538: true, 539: true, 540: true, 541: true, 542: true, 543: true, 544: true, 545: true, 546: true, 547: true, 548: true, 549: true, 550: true, 551: true, 552: true, 553: true, 554: true, 555: true, 556: true, 557: true, 558: true, 559: true, 560: true, 561: true, 562: true, 563: true, 564: true, 565: true, 566: true, 567: true, 568: true, 569: true, 570: true, 571: true, 572: true, 573: true, 574: true, 575: true, 576: true, 577: true, 578: true, 579: true, 580: true, 581: true, 582: true, 583: true, 584: true, 585: true, 586: true, 587: true, 588: true, 589: true, 590: true, 591: true, 592: true, 593: true, 594: true, 595: true, 596: true, 597: true, 598: true, 599: true, 600: true, 601: true, 602: true, 603: true, 604: true, 605: true, 606: true, 607: true, 608: true, 609: true, 610: true, 611: true, 612: true, 613: true, 614: true, 615: true, 616: true, 617: true, 618: true, 619: true, 620: true, 621: true, 622: true, 623: true, 624: true, 625: true, 626: true, 627: true, 628: true, 629: true, 630: true, 631: true, 632: true, 633: true, 634: true, 635: true, 636: true, 637: true, 638: true, 639: true, 640: true, 641: true, 642: true, 643: true, 644: true, 645: true, 646: true, 647: true, 648: true, 649: true, 650: true, 651: true, 652: true, 653: true, 654: true, 655: true, 656: true, 657: true, 658: true, 659: true, 660: true, 661: true, 662: true, 663: true, 664: true, 665: true, 666: true, 667: true, 668: true, 669: true, 670: true, 671: true, 672: true, 673: true, 674: true, 675: true, 676: true, 677: true, 678: true, 679: true, 680: true, 681: true, 682: true, 683: true, 684: true, 685: true, 686: true, 687: true, 688: true, 689: true, 690: true, 691: true, 692: true, 693: true, 694: true, 695: true, 696: true, 697: true, 698: true, 699: true, 700: true, 701: true, 702: true, 703: true, 704: true, 705: true, 706: true, 707: true, 708: true, 709: true, 710: true, 711: true, 712: true, 713: true, 714: true, 715: true, 716: true, 717: true, 718: true, 719: true, 720: true, 721: true, 722: true, 723: true, 724: true, 725: true, 726: true, 727: true, 728: true, 729: true})"];
    //     expect.assert_eq(&s);
    // }

    // #[test]
    // fn succ_dnf() {
    //     let formula = dimacs::read_string(dimacs::SUCC_EG);
    //     let result = Default::solve(formula);
    //     let s = format!("{:?}", result);
    //     let expect = expect!["Sat({1: false, 2: true, 3: false, 4: false, 5: false, 6: true, 7: false, 8: false, 9: false, 10: true, 11: false, 12: false, 13: true, 14: false, 15: false, 16: false, 17: false, 18: false, 19: false, 20: false, 21: true, 22: false, 23: false, 24: true, 25: false, 26: false, 27: false, 28: true, 29: false, 30: false, 31: false, 32: true, 33: false, 34: false, 35: false, 36: true, 37: true, 38: false, 39: false, 40: false, 41: false, 42: false, 43: true, 44: false, 45: false, 46: false, 47: true, 48: false, 49: false, 50: false, 51: true, 52: false, 53: false, 54: false, 55: false, 56: true, 57: false, 58: false, 59: false, 60: true, 61: false, 62: false, 63: false, 64: false, 65: false, 66: false, 67: false, 68: true, 69: false, 70: false, 71: true, 72: false, 73: false, 74: false, 75: true, 76: false, 77: true, 78: false, 79: false, 80: false, 81: false, 82: true, 83: false, 84: false, 85: false, 86: true, 87: false, 88: true, 89: false, 90: false, 91: false, 92: false, 93: false, 94: true, 95: false, 96: false, 97: false, 98: false, 99: false, 100: false, 101: true, 102: false, 103: false, 104: true, 105: false, 106: true, 107: true, 108: false, 109: true, 110: true, 111: false, 112: true, 113: true, 114: false, 115: true, 116: true, 117: true, 118: true, 119: false, 120: true, 121: true, 122: true, 123: false, 124: true, 125: true, 126: false, 127: false, 128: true, 129: true, 130: true, 131: true, 132: false, 133: true, 134: true, 135: true, 136: false, 137: true, 138: false, 139: true, 140: true})"];
    //     expect.assert_eq(&s);
    // }

    // #[test]
    // fn fail_dnf() {
    //     let formula = dimacs::read_string(dimacs::FAIL_EG);
    //     let result = Default::solve(formula);
    //     let s = format!("{:?}", result);
    //     let expect = expect!["Unsat"];
    //     expect.assert_eq(&s);
    // }
}
