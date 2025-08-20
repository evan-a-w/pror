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
    fn stepped2_with_assumptions() {
        use std::fmt::Write;
        let formula = vec![
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
        let mut solver = Default::create(formula);
        let res = solver.run();
        writeln!(writer, "{:?}", res);
        let res = solver.run_with_assumptions(&[1]);
        writeln!(writer, "{:?}", res);
        let res = solver.run_with_assumptions(&[1, 2]);
        writeln!(writer, "{:?}", res);
        let res = solver.run_with_assumptions(&[1, 2, 5]);
        writeln!(writer, "{:?}", res);
        let res = solver.run_with_assumptions(&[6]);
        writeln!(writer, "{:?}", res);
        let res = solver.run_with_assumptions(&[1, 2, 6]);
        writeln!(writer, "{:?}", res);
        let res = solver.run_with_assumptions(&[-1, -2, -3, -4, -5]);
        writeln!(writer, "{:?}", res);
        let res = solver.run_with_assumptions(&[-1, -2, -3, -4, -5, -6]);
        writeln!(writer, "{:?}", res);
        let expect = expect![[r#"
            Sat({1: false, 2: false, 3: true, 4: false, 5: false, 6: false})
            Sat({1: true, 2: false, 3: true, 4: false, 5: false, 6: false})
            Sat({1: true, 2: true, 3: true, 4: true, 5: false, 6: false})
            Unsat
            Sat({1: false, 2: false, 3: false, 4: true, 5: false, 6: true})
            Unsat
            Sat({1: false, 2: false, 3: false, 4: false, 5: false, 6: true})
            Sat({1: false, 2: false, 3: false, 4: false, 5: false, 6: false})
        "#]];
        expect.assert_eq(writer.borrow().as_ref());
    }

    #[test]
    fn simple_satisfiable_1_incr() {
        use std::fmt::Write;
        let mut solver = Default::new_from_vec(vec![]);
        solver.add_clause(vec![1]);
        let mut writer = SharedStringWriter::new();
        let res = solver.run();
        writeln!(writer, "{:?}", res).unwrap();
        // Add again, should not change result
        solver.add_clause(vec![1]);
        let res2 = solver.run();
        writeln!(writer, "{:?}", res2).unwrap();
        let expect = expect![[r#"
Sat({1: true})
Sat({1: true})
"#]];
        expect.assert_eq(writer.borrow().as_ref());
    }

    #[test]
    fn simple_unsatisfiable_1_incr() {
        use std::fmt::Write;
        let mut solver = Default::new_from_vec(vec![]);
        solver.add_clause(vec![1]);
        let mut writer = SharedStringWriter::new();
        let res = solver.run();
        writeln!(writer, "{:?}", res).unwrap();
        solver.add_clause(vec![-1]);
        let res2 = solver.run();
        writeln!(writer, "{:?}", res2).unwrap();
        let expect = expect![[r#"
Sat({1: true})
Unsat
"#]];
        expect.assert_eq(writer.borrow().as_ref());
    }

    #[test]
    fn satisfiable_3_vars_multiple_clauses_incr() {
        use std::fmt::Write;
        let mut solver = Default::new_from_vec(vec![]);
        let mut writer = SharedStringWriter::new();
        solver.add_clause(vec![1, 2]);
        let res1 = solver.run();
        writeln!(writer, "{:?}", res1).unwrap();
        solver.add_clause(vec![-2, 3]);
        let res2 = solver.run();
        writeln!(writer, "{:?}", res2).unwrap();
        solver.add_clause(vec![-1, -3]);
        let res3 = solver.run();
        writeln!(writer, "{:?}", res3).unwrap();
        let expect = expect![[r#"
            Sat({1: true, 2: true})
            Sat({1: true, 2: false, 3: true})
            Sat({1: false, 2: true, 3: true})
        "#]];
        expect.assert_eq(writer.borrow().as_ref());
    }

    #[test]
    fn stepped4_incr() {
        use std::fmt::Write;
        let formula = vec![
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
        let mut solver = Default::new_from_vec(vec![]);
        for clause in formula {
            solver.add_clause(clause.clone());
        }
        let mut writer = SharedStringWriter::new();
        let res = solver.run();
        writeln!(writer, "{:?}", res).unwrap();
        let expect = expect![[r#"
            Sat({1: false, 2: false, 3: true, 4: false, 5: false, 6: false})
        "#]];
        expect.assert_eq(writer.borrow().as_ref());
    }

    #[test]
    fn stepped1_incr() {
        use std::fmt::Write;
        let formula = vec![vec![1]];
        let mut solver = Default::new_from_vec(vec![]);
        for clause in &formula {
            solver.add_clause(clause.clone());
        }
        let mut writer = SharedStringWriter::new();
        let res = solver.run();
        writeln!(writer, "{:?}", res).unwrap();
        let expect = expect![[r#"
Sat({1: true})
"#]];
        expect.assert_eq(writer.borrow().as_ref());
    }
}
