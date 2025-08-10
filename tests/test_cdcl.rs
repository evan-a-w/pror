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
        let expect = expect!["Sat({1: false, 2: true, 3: true})"];
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
        step_and_print(&mut writer, &mut solver, None);
        let expect = expect![[r#"
            adding watched literals 1 and 2 for clause ("(1 2 3)")
            adding watched literals 1 and 2 for clause ("(1 2 -3)")
            adding watched literals -2 and 4 for clause ("(-2 4)")
            adding watched literals 1 and -2 for clause ("(1 -2 -4)")
            adding watched literals -1 and 5 for clause ("(-1 5 6)")
            adding watched literals -1 and 5 for clause ("(-1 5 -6)")
            adding watched literals -5 and -6 for clause ("(-5 -6)")
            adding watched literals -1 and -5 for clause ("(-1 -5 6)")
            reacting to action: Continue(Literal { value: -1 }) at decision level 1
            adding to trail at decision level 1: -1
            updating watched clauses for literal -1
            replacing watched literal 1 with 3 in clause ("(1 2 3)")
            replacing watched literal 1 with -3 in clause ("(1 2 -3)")
            replacing watched literal 1 with -4 in clause ("(1 -2 -4)")

            Continue
            reacting to action: Continue(Literal { value: -2 }) at decision level 2
            adding to trail at decision level 2: -2
            updating watched clauses for literal -2
            found unit literal (3) while updating watched clauses for literal 2 in clause ("(1 2 3)")
            found unit literal (-3) while updating watched clauses for literal 2 in clause ("(1 2 -3)")

            Continue
            found unit clause: Literal { value: 3 } in clause ("(1 2 3)") unit clauses rn: (1 2 -3)
            adding to trail at decision level 2: 3
            updating watched clauses for literal 3
            reacting to action: Contradiction(1) at decision level 2
            undoing trail entry: 3 at decision level 2
            undoing trail entry: -2 at decision level 2
            adding watched literal 2 for unit clause ("(1 2)")

            Continue
            found unit clause: Literal { value: 2 } in clause ("(1 2)") unit clauses rn: 
            adding to trail at decision level 1: 2
            updating watched clauses for literal 2
            found unit literal (4) while updating watched clauses for literal -2 in clause ("(-2 4)")
            found unit literal (-4) while updating watched clauses for literal -2 in clause ("(1 -2 -4)")
            found unit clause: Literal { value: 4 } in clause ("(-2 4)") unit clauses rn: (1 -2 -4)
            adding to trail at decision level 1: 4
            updating watched clauses for literal 4
            reacting to action: Contradiction(3) at decision level 1
            undoing trail entry: 4 at decision level 1
            undoing trail entry: 2 at decision level 1
            undoing trail entry: -1 at decision level 1
            adding watched literal 1 for unit clause ("(1)")

            Continue
            found unit clause: Literal { value: 1 } in clause ("(1)") unit clauses rn: 
            adding to trail at decision level 0: 1
            updating watched clauses for literal 1
            replacing watched literal -1 with 6 in clause ("(-1 5 6)")
            replacing watched literal -1 with -6 in clause ("(-1 5 -6)")
            replacing watched literal -1 with 6 in clause ("(-1 -5 6)")

            Continue
            reacting to action: Continue(Literal { value: 2 }) at decision level 1
            adding to trail at decision level 1: 2
            updating watched clauses for literal 2
            found unit literal (4) while updating watched clauses for literal -2 in clause ("(-2 4)")

            Continue
            found unit clause: Literal { value: 4 } in clause ("(-2 4)") unit clauses rn: 
            adding to trail at decision level 1: 4
            updating watched clauses for literal 4

            Continue
            reacting to action: Continue(Literal { value: 6 }) at decision level 2
            adding to trail at decision level 2: 6
            updating watched clauses for literal 6
            found unit literal (5) while updating watched clauses for literal -6 in clause ("(-1 5 -6)")
            found unit literal (-5) while updating watched clauses for literal -6 in clause ("(-5 -6)")

            Continue
            found unit clause: Literal { value: 5 } in clause ("(-1 5 -6)") unit clauses rn: (-5 -6)
            adding to trail at decision level 2: 5
            updating watched clauses for literal 5
            reacting to action: Contradiction(6) at decision level 2
            undoing trail entry: 5 at decision level 2
            undoing trail entry: 6 at decision level 2
            undoing trail entry: 4 at decision level 1
            undoing trail entry: 2 at decision level 1
            adding watched literal -6 for unit clause ("(-1 -6)")

            Continue
            found unit clause: Literal { value: -6 } in clause ("(-1 -6)") unit clauses rn: 
            adding to trail at decision level 0: -6
            updating watched clauses for literal -6
            found unit literal (5) while updating watched clauses for literal 6 in clause ("(-1 5 6)")
            found unit literal (-5) while updating watched clauses for literal 6 in clause ("(-1 -5 6)")
            found unit clause: Literal { value: 5 } in clause ("(-1 5 6)") unit clauses rn: (-1 -5 6)
            adding to trail at decision level 0: 5
            updating watched clauses for literal 5
            reacting to action: Contradiction(7) at decision level 0

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
            adding watched literals 3 and -5 for clause ("(3 -5 6)")
            adding watched literals -2 and -3 for clause ("(-2 -3 -4 -5 6)")
            adding watched literals 1 and 4 for clause ("(1 4 -5 -6)")
            adding watched literals 1 and 2 for clause ("(1 2 3 -4 5 6)")
            adding watched literals -1 and -2 for clause ("(-1 -2 -3 4 -5 6)")
            adding watched literals -2 and 3 for clause ("(-2 3 4 -6)")
            adding watched literals -1 and 2 for clause ("(-1 2 3)")
            adding watched literals -3 and -4 for clause ("(-3 -4 5 -6)")
            adding watched literals -1 and 2 for clause ("(-1 2 -3 -4 5 6)")
            adding watched literals -2 and -3 for clause ("(-2 -3 4 5)")
            adding watched literals -1 and -2 for clause ("(-1 -2 3 -4 -5 -6)")
            adding watched literals -2 and -6 for clause ("(-2 -6)")
            adding watched literals -1 and -2 for clause ("(-1 -2 4 5)")
            adding watched literals 1 and 2 for clause ("(1 2 3 -4 -5 -6)")
            reacting to action: Continue(Literal { value: -2 }) at decision level 1
            adding to trail at decision level 1: -2
            updating watched clauses for literal -2
            replacing watched literal 2 with 3 in clause ("(1 2 3 -4 5 6)")
            replacing watched literal 2 with 3 in clause ("(-1 2 3)")
            replacing watched literal 2 with -3 in clause ("(-1 2 -3 -4 5 6)")
            replacing watched literal 2 with 3 in clause ("(1 2 3 -4 -5 -6)")
            reacting to action: Continue(Literal { value: 3 }) at decision level 2
            adding to trail at decision level 2: 3
            updating watched clauses for literal 3
            replacing watched literal -3 with 5 in clause ("(-3 -4 5 -6)")
            replacing watched literal -3 with -4 in clause ("(-1 2 -3 -4 5 6)")
            reacting to action: Continue(Literal { value: -4 }) at decision level 3
            adding to trail at decision level 3: -4
            updating watched clauses for literal -4
            replacing watched literal 4 with -5 in clause ("(1 4 -5 -6)")
            reacting to action: Continue(Literal { value: -5 }) at decision level 4
            adding to trail at decision level 4: -5
            updating watched clauses for literal -5
            reacting to action: Continue(Literal { value: -6 }) at decision level 5
            adding to trail at decision level 5: -6
            updating watched clauses for literal -6
            reacting to action: Continue(Literal { value: -1 }) at decision level 6
            adding to trail at decision level 6: -1
            updating watched clauses for literal -1
            Sat({1: false, 2: false, 3: true, 4: false, 5: false, 6: false})
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
            adding watched literals 1 and 3 for clause ("(1 3 4 -5 6 9 -10 12 -13 14 15)")
            adding watched literals 1 and -3 for clause ("(1 -3 -4 5 -6 -7 8 9 -10 11 -12 -13 14 -15)")
            adding watched literals -4 and -5 for clause ("(-4 -5 -6 -7 8 10 12 -13 15)")
            adding watched literals 5 and 8 for clause ("(5 8 -11 -12 -13 14 -15)")
            adding watched literals 3 and 5 for clause ("(3 5 8 10 -11 12 13 -14)")
            adding watched literals -4 and -13 for clause ("(-4 -13)")
            adding watched literals 11 and 14 for clause ("(11 14)")
            adding watched literals -5 and -6 for clause ("(-5 -6 13 -14)")
            adding watched literals 4 and -5 for clause ("(4 -5 -14)")
            adding watched literals 2 and -6 for clause ("(2 -6 8 12)")
            adding watched literals 1 and 2 for clause ("(1 2 -3 -4 -5 6 7 8 9 10 11 12 -13 15)")
            adding watched literals 1 and -2 for clause ("(1 -2 -4 5 9 -11 12 13 -14 -15)")
            adding watched literals 6 and -7 for clause ("(6 -7 -12 15)")
            adding watched literals 1 and -3 for clause ("(1 -3 5 7 -8 -9 10 11 -12 13 -14 -15)")
            adding watched literals -1 and -2 for clause ("(-1 -2 -3 -4 -5 -6 -9 -10 -11 -12 -13 14)")
            adding watched literals -2 and -3 for clause ("(-2 -3 -4 -5 6 7 8 -9 -10 11 14)")
            adding watched literals 1 and -2 for clause ("(1 -2 3 -4 5 6 7 -8 9 10 11 12 -13 -14 -15)")
            adding watched literals 1 and 2 for clause ("(1 2 3 -4 8 -10 -14 15)")
            adding watched literals 3 and 9 for clause ("(3 9)")
            adding watched literals -2 and -4 for clause ("(-2 -4 -5 7 -8)")
            adding watched literals 1 and -2 for clause ("(1 -2 3 -7 -11 12 -14 -15)")
            adding watched literals -3 and -5 for clause ("(-3 -5 8)")
            adding watched literals -1 and -2 for clause ("(-1 -2 3 -4 -6 -8 -10 12 13 -14 -15)")
            adding watched literals -1 and -3 for clause ("(-1 -3 5 7 8 -9 -11 -13 -14)")
            adding watched literal -3 for unit clause ("(-3)")
            adding watched literals -1 and 2 for clause ("(-1 2 -3 4 -5 6 7 -8 -9 10 -11 -12 -13 14 15)")
            adding watched literals -2 and -5 for clause ("(-2 -5 -6 7 8 -9 10 12 -15)")
            adding watched literals 13 and 15 for clause ("(13 15)")
            adding watched literals -1 and 2 for clause ("(-1 2 -3 5 6 9 12 14 -15)")
            adding watched literals -1 and -4 for clause ("(-1 -4 11 13)")
            adding watched literals -5 and 6 for clause ("(-5 6 12 14)")
            adding watched literals 1 and 3 for clause ("(1 3 -4 -6 7 9 10 13 -15)")
            adding watched literals -3 and -8 for clause ("(-3 -8)")
            adding watched literals -2 and 7 for clause ("(-2 7 8 -12 14)")
            adding watched literals 2 and 3 for clause ("(2 3 -9 -11 -12)")
            adding watched literals 4 and -10 for clause ("(4 -10)")
            adding watched literals 1 and -4 for clause ("(1 -4 5 6 7 -8 9 11)")
            adding watched literals -1 and -3 for clause ("(-1 -3 5 6 7 8 -11 -13 -14 15)")
            adding watched literals 1 and 2 for clause ("(1 2 3 5 -7 9)")
            adding watched literals 3 and 9 for clause ("(3 9 -11)")
            adding watched literals 1 and 2 for clause ("(1 2 4 6 -7 9 10 11 12 -15)")
            adding watched literals -6 and 9 for clause ("(-6 9)")
            adding watched literals 1 and -2 for clause ("(1 -2 -3 -4 5 -6 -7 8 9 10 -11 12 13 14 15)")
            adding watched literals -8 and -9 for clause ("(-8 -9 -10)")
            adding watched literals -2 and 3 for clause ("(-2 3 6 8 10 12 -14 -15)")
            adding watched literals 4 and 6 for clause ("(4 6 -7 -9 15)")
            adding watched literals -2 and 4 for clause ("(-2 4 8 -9 10 -12 -14)")
            adding watched literal -10 for unit clause ("(-10)")
            adding watched literals -3 and -14 for clause ("(-3 -14)")
            adding watched literals 1 and 2 for clause ("(1 2 4 5 6 7 -9 10 -11 12)")
            adding watched literals -1 and -6 for clause ("(-1 -6 11)")
            adding watched literals -3 and -7 for clause ("(-3 -7 8 -10 11 -14 15)")
            adding watched literals 1 and 2 for clause ("(1 2 3 4 5 6 7 -8 9 10 -12 -13 -14 -15)")
            adding watched literals -1 and 3 for clause ("(-1 3 -5 -12)")
            adding watched literals 1 and 2 for clause ("(1 2 -4 5 6 -7 8 -9 10 11 12 13 14 -15)")
            adding watched literals 3 and -10 for clause ("(3 -10)")
            adding watched literals 1 and 2 for clause ("(1 2 3 -4 -5 6 -7 8 9 -10 11 12 -13 14 15)")
            adding watched literals 3 and -5 for clause ("(3 -5 6 7 -9 -14 15)")
            adding watched literals -1 and -3 for clause ("(-1 -3 -5 -7 -8 -11 12 -15)")
            adding watched literals -1 and -2 for clause ("(-1 -2 3 -5 6 -7 -8 -9 11 -12 -13 14 15)")
            adding watched literals 1 and 2 for clause ("(1 2 3 -4 6 -8 -9 -10 -12 13 14 -15)")
            adding watched literals 1 and 2 for clause ("(1 2 -3 13 14 -15)")
            adding watched literals 1 and -2 for clause ("(1 -2 3 -4 -5 6 7 8 -11 -15)")
            adding watched literal 4 for unit clause ("(4)")
            adding watched literals -2 and 4 for clause ("(-2 4 -6 12 13 -15)")
            adding watched literals -1 and 4 for clause ("(-1 4 -5 -8 9 13 -14)")
            adding watched literals -1 and 2 for clause ("(-1 2 3 6 -7 8 10 11)")
            adding watched literals 3 and -4 for clause ("(3 -4 6 -8 -10 11 -13 -14)")
            adding watched literals 1 and -3 for clause ("(1 -3 -4 5 7 8 -9 -10 11 -12 13)")
            adding watched literals 1 and -2 for clause ("(1 -2 -3 7 -10 11 12 13 -14)")
            adding watched literals -6 and 7 for clause ("(-6 7 -8 -10 14)")
            adding watched literals -1 and -5 for clause ("(-1 -5 -7 8 -11 -14)")
            adding watched literals 2 and -3 for clause ("(2 -3 7 8 14 15)")
            adding watched literal -3 for unit clause ("(-3)")
            adding watched literals -1 and 3 for clause ("(-1 3 -5 9 10 -11 -13 -14 15)")
            adding watched literals -2 and -3 for clause ("(-2 -3 4 -5 7 -9 11)")
            adding watched literals -3 and -6 for clause ("(-3 -6 -7 8)")
            adding watched literals -2 and -5 for clause ("(-2 -5 -8 -9 10 -11 14)")
            adding watched literals -10 and 11 for clause ("(-10 11 -14)")
            adding watched literals 3 and -5 for clause ("(3 -5 8 11 12 -13 15)")
            adding watched literals 2 and -3 for clause ("(2 -3 8 12 -13 -14)")
            adding watched literals -1 and 2 for clause ("(-1 2 -3 4 5 -8 10 11 -12 -14 15)")
            adding watched literals 1 and 2 for clause ("(1 2 4 -5 7 8 -10 -11)")
            found unit clause: Literal { value: -3 } in clause ("(-3)") unit clauses rn: (-10); (4); (-3)
            adding to trail at decision level 0: -3
            updating watched clauses for literal -3
            replacing watched literal 3 with 4 in clause ("(1 3 4 -5 6 9 -10 12 -13 14 15)")
            replacing watched literal 3 with 8 in clause ("(3 5 8 10 -11 12 13 -14)")
            found unit literal (9) while updating watched clauses for literal 3 in clause ("(3 9)")
            replacing watched literal 3 with -4 in clause ("(1 3 -4 -6 7 9 10 13 -15)")
            replacing watched literal 3 with -9 in clause ("(2 3 -9 -11 -12)")
            replacing watched literal 3 with -11 in clause ("(3 9 -11)")
            replacing watched literal 3 with 6 in clause ("(-2 3 6 8 10 12 -14 -15)")
            replacing watched literal 3 with -5 in clause ("(-1 3 -5 -12)")
            found unit literal (-10) while updating watched clauses for literal 3 in clause ("(3 -10)")
            replacing watched literal 3 with 6 in clause ("(3 -5 6 7 -9 -14 15)")
            replacing watched literal 3 with 6 in clause ("(3 -4 6 -8 -10 11 -13 -14)")
            replacing watched literal 3 with -5 in clause ("(-1 3 -5 9 10 -11 -13 -14 15)")
            replacing watched literal 3 with 8 in clause ("(3 -5 8 11 12 -13 15)")
            found unit clause: Literal { value: 9 } in clause ("(3 9)") unit clauses rn: (-10); (3 -10); (4); (-3)
            adding to trail at decision level 0: 9
            updating watched clauses for literal 9
            replacing watched literal -9 with -11 in clause ("(2 3 -9 -11 -12)")
            replacing watched literal -9 with -10 in clause ("(-8 -9 -10)")
            found unit clause: Literal { value: -10 } in clause ("(-10)") unit clauses rn: (3 -10); (4); (-3)
            adding to trail at decision level 0: -10
            updating watched clauses for literal -10
            found unit clause: Literal { value: 4 } in clause ("(4)") unit clauses rn: (-3)
            adding to trail at decision level 0: 4
            updating watched clauses for literal 4
            replacing watched literal -4 with -6 in clause ("(-4 -5 -6 -7 8 10 12 -13 15)")
            found unit literal (-13) while updating watched clauses for literal -4 in clause ("(-4 -13)")
            replacing watched literal -4 with -5 in clause ("(-2 -4 -5 7 -8)")
            replacing watched literal -4 with 11 in clause ("(-1 -4 11 13)")
            found unit clause: Literal { value: -13 } in clause ("(-4 -13)") unit clauses rn: (-3)
            adding to trail at decision level 0: -13
            updating watched clauses for literal -13
            found unit literal (15) while updating watched clauses for literal 13 in clause ("(13 15)")
            found unit clause: Literal { value: 15 } in clause ("(13 15)") unit clauses rn: (-3)
            adding to trail at decision level 0: 15
            updating watched clauses for literal 15
            reacting to action: Continue(Literal { value: 8 }) at decision level 1
            adding to trail at decision level 1: 8
            updating watched clauses for literal 8
            reacting to action: Continue(Literal { value: -5 }) at decision level 2
            adding to trail at decision level 2: -5
            updating watched clauses for literal -5
            reacting to action: Continue(Literal { value: -14 }) at decision level 3
            adding to trail at decision level 3: -14
            updating watched clauses for literal -14
            found unit literal (11) while updating watched clauses for literal 14 in clause ("(11 14)")
            found unit clause: Literal { value: 11 } in clause ("(11 14)") unit clauses rn: 
            adding to trail at decision level 3: 11
            updating watched clauses for literal 11
            replacing watched literal -11 with -12 in clause ("(2 3 -9 -11 -12)")
            reacting to action: Continue(Literal { value: 12 }) at decision level 4
            adding to trail at decision level 4: 12
            updating watched clauses for literal 12
            found unit literal (2) while updating watched clauses for literal -12 in clause ("(2 3 -9 -11 -12)")
            found unit clause: Literal { value: 2 } in clause ("(2 3 -9 -11 -12)") unit clauses rn: 
            adding to trail at decision level 4: 2
            updating watched clauses for literal 2
            reacting to action: Continue(Literal { value: 6 }) at decision level 5
            adding to trail at decision level 5: 6
            updating watched clauses for literal 6
            reacting to action: Continue(Literal { value: 1 }) at decision level 6
            adding to trail at decision level 6: 1
            updating watched clauses for literal 1
            reacting to action: Continue(Literal { value: 7 }) at decision level 7
            adding to trail at decision level 7: 7
            updating watched clauses for literal 7
            Sat({1: true, 2: true, 3: false, 4: true, 5: false, 6: true, 7: true, 8: true, 9: true, 10: false, 11: true, 12: true, 13: false, 14: false, 15: true})
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
            adding watched literals -1 and -2 for clause ("(-1 -2 -3 -4 5 6 -7 -8)")
            adding watched literals 1 and -7 for clause ("(1 -7)")
            adding watched literals -1 and 2 for clause ("(-1 2 3 -4 5 -6 7 8)")
            adding watched literals 2 and -3 for clause ("(2 -3 -4 -5 -6)")
            adding watched literals -2 and 3 for clause ("(-2 3 6 -7)")
            adding watched literals -2 and -4 for clause ("(-2 -4 -5 6 7 8)")
            adding watched literals 1 and 2 for clause ("(1 2 -3 -4 -5 -6 -8)")
            adding watched literal 7 for unit clause ("(7)")
            adding watched literals -1 and -5 for clause ("(-1 -5 -7 -8)")
            adding watched literals -4 and -8 for clause ("(-4 -8)")
            adding watched literals 3 and 4 for clause ("(3 4)")
            adding watched literals -2 and -8 for clause ("(-2 -8)")
            adding watched literals -1 and 2 for clause ("(-1 2 3 -4 6)")
            adding watched literals -1 and 2 for clause ("(-1 2 3 -4 5 -6 -7 -8)")
            adding watched literals 1 and 2 for clause ("(1 2 6 7)")
            adding watched literals -1 and 3 for clause ("(-1 3 6)")
            adding watched literals -1 and -2 for clause ("(-1 -2 3 -4 5 -6 -7 -8)")
            adding watched literals -1 and -2 for clause ("(-1 -2 3 -5 8)")
            adding watched literals -1 and -2 for clause ("(-1 -2 3 -4 -5 6)")
            adding watched literal 4 for unit clause ("(4)")
            adding watched literals 2 and -4 for clause ("(2 -4 -5 6 7 -8)")
            adding watched literals 1 and -8 for clause ("(1 -8)")
            adding watched literal 4 for unit clause ("(4)")
            adding watched literals 2 and 3 for clause ("(2 3 4 -5 6 7 -8)")
            adding watched literals -3 and 4 for clause ("(-3 4 6 -8)")
            adding watched literals 2 and -3 for clause ("(2 -3 -4 6 7)")
            adding watched literal -4 for unit clause ("(-4)")
            adding watched literal 1 for unit clause ("(1)")
            adding watched literals 1 and 3 for clause ("(1 3 -5 -6)")
            adding watched literals 4 and 5 for clause ("(4 5 6 7 -8)")
            adding watched literals -1 and 2 for clause ("(-1 2 -3 4 5 -6 -7 -8)")
            adding watched literals 1 and 2 for clause ("(1 2 3 -4 5 6 7 -8)")
            adding watched literals 2 and -3 for clause ("(2 -3 -4 5 -6 7 -8)")
            adding watched literals -1 and 2 for clause ("(-1 2 3 -6 -7 -8)")
            adding watched literals -1 and -2 for clause ("(-1 -2 3 -4 -6)")
            adding watched literals 2 and -4 for clause ("(2 -4 5 6)")
            adding watched literals -3 and 6 for clause ("(-3 6)")
            adding watched literals -1 and -2 for clause ("(-1 -2 3 -4 -8)")
            adding watched literals 2 and -3 for clause ("(2 -3 -4 -6 -7 -8)")
            adding watched literals -1 and 2 for clause ("(-1 2 3 -4 -5 6 7 -8)")
            adding watched literals -1 and 4 for clause ("(-1 4 5 -6 8)")
            adding watched literals 4 and -5 for clause ("(4 -5 -7)")
            adding watched literals 1 and 2 for clause ("(1 2 3 -4 6 -7 -8)")
            adding watched literal -1 for unit clause ("(-1)")
            adding watched literals 1 and 2 for clause ("(1 2 3 4 5 -6 7 -8)")
            adding watched literal -7 for unit clause ("(-7)")
            adding watched literals 2 and -4 for clause ("(2 -4 -6 7 -8)")
            adding watched literal -2 for unit clause ("(-2)")
            adding watched literals -3 and -6 for clause ("(-3 -6 -8)")
            adding watched literals -1 and 2 for clause ("(-1 2 3 4 5 -6 -8)")
            adding watched literals 5 and 6 for clause ("(5 6)")
            adding watched literals 6 and 7 for clause ("(6 7)")
            adding watched literals -5 and 6 for clause ("(-5 6 -7)")
            adding watched literals -1 and 3 for clause ("(-1 3 5 6 -8)")
            adding watched literals 2 and -4 for clause ("(2 -4 5 7 8)")
            adding watched literals -1 and 3 for clause ("(-1 3 4 5)")
            adding watched literals 1 and -2 for clause ("(1 -2 -3 5 -6 -7 -8)")
            adding watched literals -1 and -2 for clause ("(-1 -2 -3 4 5)")
            adding watched literals -1 and 2 for clause ("(-1 2 -3 -4 5 -6 -8)")
            adding watched literals -1 and -2 for clause ("(-1 -2 3 4 7 -8)")
            adding watched literals -2 and 3 for clause ("(-2 3)")
            adding watched literals -1 and 3 for clause ("(-1 3 -4 5 -6 -8)")
            adding watched literals 1 and 2 for clause ("(1 2)")
            adding watched literals 1 and 2 for clause ("(1 2 3 -4 5 6 7 8)")
            adding watched literals 1 and 2 for clause ("(1 2 -4 5 6 -7 -8)")
            adding watched literals 1 and -2 for clause ("(1 -2 -3 -4 -5 6 8)")
            adding watched literals -1 and -2 for clause ("(-1 -2 -3 -4 -5 6 7 -8)")
            adding watched literals -1 and 2 for clause ("(-1 2 4 -6 -7 -8)")
            adding watched literals 4 and 5 for clause ("(4 5)")
            adding watched literals 2 and -3 for clause ("(2 -3 -8)")
            adding watched literals 2 and -5 for clause ("(2 -5 -8)")
            adding watched literals -1 and 2 for clause ("(-1 2 -5 -6)")
            adding watched literals -1 and -2 for clause ("(-1 -2 3 -4 -7 -8)")
            adding watched literals -3 and -7 for clause ("(-3 -7 -8)")
            adding watched literals 2 and -3 for clause ("(2 -3 5 -6 -8)")
            adding watched literals -1 and -2 for clause ("(-1 -2 3 -4 -5 -6 -7)")
            adding watched literals 1 and -2 for clause ("(1 -2 3 -4 -5 6 -7 -8)")
            adding watched literals -2 and -5 for clause ("(-2 -5 -7 8)")
            adding watched literals 1 and 4 for clause ("(1 4 -7)")
            adding watched literals 2 and -6 for clause ("(2 -6 8)")
            adding watched literals 1 and -2 for clause ("(1 -2 -3 -4 5 -6 7 -8)")
            adding watched literal -4 for unit clause ("(-4)")
            adding watched literals 2 and 5 for clause ("(2 5 6 7 8)")
            adding watched literals 1 and -4 for clause ("(1 -4)")
            adding watched literals 2 and 3 for clause ("(2 3 -4 -6 7 -8)")
            adding watched literals -1 and 2 for clause ("(-1 2 3 -4 -5 -6 7 -8)")
            adding watched literals 1 and -2 for clause ("(1 -2 3 4 5 6 7 -8)")
            adding watched literals -5 and -6 for clause ("(-5 -6 -7)")
            adding watched literals -1 and 2 for clause ("(-1 2 3 4 5 6 7 -8)")
            adding watched literals -2 and 3 for clause ("(-2 3 -4 -5 -6 -7 -8)")
            adding watched literals 4 and 8 for clause ("(4 8)")
            adding watched literals 1 and 2 for clause ("(1 2 -3 4 -5 -6 7 -8)")
            adding watched literal -8 for unit clause ("(-8)")
            adding watched literals 4 and -5 for clause ("(4 -5 6)")
            adding watched literals 1 and -2 for clause ("(1 -2)")
            adding watched literals 4 and -5 for clause ("(4 -5 -6 7 -8)")
            adding watched literals -3 and -5 for clause ("(-3 -5 -7)")
            adding watched literals 1 and -2 for clause ("(1 -2 -3 -6 7 8)")
            adding watched literals 2 and 4 for clause ("(2 4 7)")
            adding watched literals -1 and 2 for clause ("(-1 2 -5 -7 -8)")
            adding watched literals -1 and -2 for clause ("(-1 -2 -5 -6 8)")
            adding watched literals 1 and 2 for clause ("(1 2 3 -5 -6 7 8)")
            adding watched literals 5 and 6 for clause ("(5 6 8)")
            adding watched literals 1 and -2 for clause ("(1 -2 -4 5 -6 7 -8)")
            adding watched literal 6 for unit clause ("(6)")
            adding watched literals 2 and 5 for clause ("(2 5 -7)")
            adding watched literals 1 and 2 for clause ("(1 2 -4 5 -6 7)")
            adding watched literals -1 and -2 for clause ("(-1 -2 -3 -4 -5 -6 -7 8)")
            adding watched literals 1 and 2 for clause ("(1 2 5 7 -8)")
            adding watched literals -1 and 2 for clause ("(-1 2 -3 -4 5 6 7 -8)")
            adding watched literals 1 and 2 for clause ("(1 2 -3 -4 6 7 8)")
            adding watched literal 5 for unit clause ("(5)")
            adding watched literals 1 and -2 for clause ("(1 -2 4 5 7 -8)")
            adding watched literals 2 and -4 for clause ("(2 -4)")
            adding watched literals -1 and 7 for clause ("(-1 7)")
            adding watched literals 1 and 2 for clause ("(1 2 3 -4 -5 -6 -7 8)")
            adding watched literals 7 and -8 for clause ("(7 -8)")
            adding watched literal -8 for unit clause ("(-8)")
            adding watched literals 1 and 3 for clause ("(1 3 8)")
            adding watched literals -1 and 2 for clause ("(-1 2 -3 6 7 -8)")
            adding watched literals 2 and -4 for clause ("(2 -4)")
            adding watched literals 3 and 5 for clause ("(3 5 -7 8)")
            adding watched literals 1 and 2 for clause ("(1 2 -3 -4 5 -6 -7)")
            adding watched literals 1 and 3 for clause ("(1 3 4 -5 -6 7 -8)")
            adding watched literals -1 and -2 for clause ("(-1 -2 -3 4 5 -6 7 -8)")
            adding watched literals -2 and -3 for clause ("(-2 -3 -4 -8)")
            adding watched literals 3 and 6 for clause ("(3 6)")
            adding watched literals -1 and -2 for clause ("(-1 -2 -3 -4 -6 -7 8)")
            adding watched literals 1 and 2 for clause ("(1 2 -3 -4 5 -6 7 8)")
            adding watched literals -1 and 3 for clause ("(-1 3 4 -5 -8)")
            adding watched literals -1 and -2 for clause ("(-1 -2 3 7 -8)")
            found unit clause: Literal { value: 7 } in clause ("(7)") unit clauses rn: (4); (4); (-4); (1); (-1); (-7); (-2); (-4); (-8); (6); (5); (-8)
            adding to trail at decision level 0: 7
            updating watched clauses for literal 7
            found unit literal (1) while updating watched clauses for literal -7 in clause ("(1 -7)")
            reacting to action: Contradiction(45) at decision level 0
            Unsat
        "#]];
        expect.assert_eq(writer.borrow().as_ref());
    }

    #[test]
    fn sudoku_dnf() {
        let formula = dimacs::read_string(dimacs::SUDOKU);
        let result = Default::solve(formula);
        assert!(matches!(result, SatResult::Sat(_)));
    }

    #[test]
    fn succ_dnf() {
        let formula = dimacs::read_string(dimacs::SUCC_EG);
        let result = Default::solve(formula);
        assert!(matches!(result, SatResult::Sat(_)));
    }

    #[test]
    fn succ_factor() {
        let formula = dimacs::read_string(dimacs::FACTOR_1234321);
        let result = Default::solve(formula);
        assert!(matches!(result, SatResult::Sat(_)));
    }

    // #[test]
    // fn fail_factor() {
    //     let formula = dimacs::read_string(dimacs::FACTOR_1235321);
    //     let result = Default::solve(formula);
    //     assert!(matches!(result, SatResult::Unsat));
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
