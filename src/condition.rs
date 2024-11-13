use std::{str::FromStr, sync::Arc};

use egglog::{
    ast::{Span, Symbol},
    constraint::{SimpleTypeConstraint, TypeConstraint},
    sort::{BoolSort, Sort},
    ArcSort, PrimitiveLike,
};
use ruler::enumo::Sexp;

#[derive(Debug)]
pub struct DummySort {
    // the language that a condition will operate on
    sort: ArcSort,
}

impl Sort for DummySort {
    fn name(&self) -> Symbol {
        "dummy".into()
    }

    fn as_arc_any(
        self: std::sync::Arc<Self>,
    ) -> std::sync::Arc<dyn std::any::Any + Send + Sync + 'static> {
        self
    }

    fn make_expr(
        &self,
        _egraph: &egglog::EGraph,
        _value: egglog::Value,
    ) -> (usize, egglog::ast::Expr) {
        (0, egglog::ast::Expr::lit_no_span(Symbol::from("dummy")))
    }

    fn register_primitives(self: std::sync::Arc<Self>, info: &mut egglog::TypeInfo) {
        info.add_primitive(Condition {
            name: "condition".into(),
            sort: self.sort.clone(),
        });
    }
}

pub struct Condition {
    name: Symbol,
    sort: Arc<dyn Sort>,
}

// (condition expr) -> bool
impl PrimitiveLike for Condition {
    fn name(&self) -> Symbol {
        self.name.clone()
    }

    fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
        SimpleTypeConstraint::new(
            self.name(),
            vec![self.sort.clone(), Arc::new(BoolSort::new("bool".into()))],
            span.clone(),
        )
        .into_box()
    }

    fn apply(
        &self,
        values: &[egglog::Value],
        egraph: Option<&mut egglog::EGraph>,
    ) -> Option<egglog::Value> {
        let sexp = Sexp::from_str(&egraph?.extract_value_to_string(values[0])).unwrap();

        fn interp(sexp: &Sexp) -> i64 {
            match sexp {
                Sexp::Atom(_) => panic!(),
                Sexp::List(l) => {
                    if let Sexp::Atom(op) = &l[0] {
                        match op.as_str() {
                            "Num" => {
                                if let Sexp::Atom(a) = &l[1] {
                                    a.parse().unwrap()
                                } else {
                                    panic!()
                                }
                            }
                            "Eq" => {
                                let a = interp(&l[1]);
                                let b = interp(&l[2]);
                                if a == b {
                                    1
                                } else {
                                    0
                                }
                            }
                            _ => panic!("Weird op {}", op),
                        }
                    } else {
                        panic!()
                    }
                }
            }
        }

        println!("result of evaluating {}: {}", sexp, interp(&sexp) != 0);

        Some(egglog::Value::from(interp(&sexp) != 0))
    }
}

pub mod tests {
    use egglog::{sort::EqSort, SerializeConfig};

    use super::*;

    #[test]
    fn test_condition_create() {
        let math_sort = Arc::new(EqSort {
            name: "Math".into(),
        });
        let dummy_sort = Arc::new(DummySort {
            sort: math_sort.clone(),
        });

        let mut egraph = egglog::EGraph::default();

        egraph.add_arcsort(math_sort.clone()).unwrap();
        egraph.add_arcsort(dummy_sort).unwrap();

        egraph
            .parse_and_run_program(
                None,
                r#"
                (function Num (i64) Math)
                (function Mul (Math Math) Math)
                (function Eq (Math Math) Math)

                (relation universe (Math))
                (relation has-val (Math bool))
                "#,
            )
            .unwrap();

        egraph
            .parse_and_run_program(
                None,
                r#"
                (rule
                    (
                     (universe ?e)
                     (= ?e (Eq ?a ?b))
                    )
                    ((has-val ?e (condition ?e)))
                )

                (rule
                    (
                     (has-val ?c true)
                     (= ?c (Eq ?e (Num 1)))
                    )
                    (
                     (union ?e (Mul ?e ?e))
                    )
                )
                "#,
            )
            .unwrap();

        egraph
            .parse_and_run_program(
                None,
                r#"
                (universe (Num 1))
                (universe (Eq (Num 1) (Num 1)))
            "#,
            )
            .unwrap();

        egraph.parse_and_run_program(None, "(run 1000)").unwrap();

        let serialized = egraph.serialize(SerializeConfig::default());
        serialized.to_svg_file("condition.svg").unwrap();
    }
}

// small accessibility nit: slide 4 has similar colors.
