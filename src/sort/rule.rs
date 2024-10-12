use std::sync::{Arc, Mutex};

use crate::Cost;
use egglog::{
    ast::Symbol,
    constraint::SimpleTypeConstraint,
    sort::{FromSort, IntoSort, Sort},
    util::{IndexMap, IndexSet},
    ArcSort, PrimitiveLike, Term, Value,
};

#[derive(Debug)]
pub struct RuleSort {
    // TODO: make private
    pub name: Symbol,
    pub language: ArcSort,
    pub predicate_language: ArcSort,
    // condition, (lhs, rhs)
    pub rules: Mutex<IndexSet<(Option<Value>, Value, Value)>>,
}

struct ValueRule {
    condition: Option<Value>,
    lhs: Value,
    rhs: Value,
}

impl IntoSort for ValueRule {
    type Sort = RuleSort;
    fn store(self, sort: &Self::Sort) -> Option<Value> {
        let (i, _) = sort
            .rules
            .lock()
            .unwrap()
            .insert_full((self.condition, self.lhs, self.rhs));
        Some(Value {
            tag: sort.name,
            bits: i as u64,
        })
    }
}

impl FromSort for ValueRule {
    type Sort = RuleSort;
    fn load(sort: &Self::Sort, value: &Value) -> Self {
        let (condition, lhs, rhs) = sort
            .rules
            .lock()
            .unwrap()
            .get_index(value.bits as usize)
            .unwrap()
            .clone();
        ValueRule {
            condition: condition.clone(),
            lhs: lhs.clone(),
            rhs: rhs.clone(),
        }
    }
}

impl Sort for RuleSort {
    fn name(&self) -> Symbol {
        self.name
    }

    fn as_arc_any(
        self: std::sync::Arc<Self>,
    ) -> std::sync::Arc<dyn std::any::Any + Send + Sync + 'static> {
        self
    }

    fn make_expr(
        &self,
        egraph: &egglog::EGraph,
        value: egglog::Value,
    ) -> (Cost, egglog::ast::Expr) {
        let rule = ValueRule::load(self, &value);
        let (lhs_termdag, lhs) = egraph.extract_value(rule.lhs);
        let (rhs_termdag, rhs) = egraph.extract_value(rule.rhs);

        let lhs_expr = lhs_termdag.term_to_expr(&lhs);
        let rhs_expr = rhs_termdag.term_to_expr(&rhs);
        match rule.condition {
            None => (
                1,
                egglog::ast::Expr::Call(
                    egglog::ast::DUMMY_SPAN.clone(),
                    "Rule".into(),
                    vec![lhs_expr, rhs_expr],
                ),
            ),
            Some(condition) => {
                let (condition_termdag, condition) = egraph.extract_value(condition);
                let condition_expr = condition_termdag.term_to_expr(&condition);
                (
                    // TODO: saturating_add cost instead of 1
                    1,
                    egglog::ast::Expr::Call(
                        egglog::ast::DUMMY_SPAN.clone(),
                        "ConditionalRule".into(),
                        vec![condition_expr, lhs_expr, rhs_expr],
                    ),
                )
            }
        }
    }

    fn register_primitives(self: Arc<Self>, info: &mut egglog::TypeInfo) {
        info.add_primitive(Ctor {
            name: format!("Rule").into(),
            rules: self.clone(),
        });
        info.add_primitive(ConditionalCtor {
            name: format!("ConditionalRule").into(),
            rules: self.clone(),
        });
    }
}

struct Ctor {
    name: Symbol,
    rules: Arc<RuleSort>,
}

impl PrimitiveLike for Ctor {
    fn name(&self) -> Symbol {
        self.name
    }

    fn apply(&self, values: &[Value], egraph: Option<&mut egglog::EGraph>) -> Option<Value> {
        self.rules
            .rules
            .lock()
            .unwrap()
            .iter()
            .for_each(|(condition, lhs, rhs)| {
                println!("condition: {:?}, lhs: {:?}, rhs: {:?}", condition, lhs, rhs);
            });
        ValueRule {
            condition: None,
            lhs: values[0].clone(),
            rhs: values[1].clone(),
        }
        .store(&self.rules)
    }

    fn get_type_constraints(
        &self,
        span: &egglog::ast::Span,
    ) -> Box<dyn egglog::constraint::TypeConstraint> {
        SimpleTypeConstraint::new(
            self.name(),
            vec![
                self.rules.language.clone(),
                self.rules.language.clone(),
                self.rules.clone(),
            ],
            span.clone(),
        )
        .into_box()
    }
}

struct ConditionalCtor {
    name: Symbol,
    rules: Arc<RuleSort>,
}

impl PrimitiveLike for ConditionalCtor {
    fn name(&self) -> Symbol {
        self.name
    }

    fn apply(&self, values: &[Value], _egraph: Option<&mut egglog::EGraph>) -> Option<Value> {
        ValueRule {
            condition: Some(values[0].clone()),
            lhs: values[1].clone(),
            rhs: values[2].clone(),
        }
        .store(&self.rules)
    }

    fn get_type_constraints(
        &self,
        span: &egglog::ast::Span,
    ) -> Box<dyn egglog::constraint::TypeConstraint> {
        SimpleTypeConstraint::new(
            self.name(),
            vec![
                self.rules.predicate_language.clone(),
                self.rules.language.clone(),
                self.rules.language.clone(),
                self.rules.clone(),
            ],
            span.clone(),
        )
        .into_box()
    }
}

pub mod tests {
    use super::*;
    use egglog::{sort::EqSort, EGraph};

    #[test]
    fn test_rule_ctors() {
        let math_sort = Arc::new(EqSort {
            name: "Math".into(),
        });
        let pred_sort = Arc::new(EqSort {
            name: "Pred".into(),
        });
        let rule_language = Arc::new(RuleSort {
            name: "Rule".into(),
            language: math_sort.clone(),
            predicate_language: pred_sort.clone(),
            rules: Mutex::new(IndexSet::default()),
        });
        let mut egraph = EGraph::default();
        egraph.add_arcsort(math_sort).unwrap();
        egraph.add_arcsort(pred_sort).unwrap();
        egraph.add_arcsort(rule_language.clone()).unwrap();
        egraph
            .parse_and_run_program(
                None,
                r#"
                (function Num (i64) Math)
                (function Eq (Math Math) Pred)
                (Rule (Num 31415926) (Num 1111))
                (ConditionalRule (Eq (Num 1) (Num 1)) (Num 31415926) (Num 1111))
                "#,
            )
            .unwrap();
        let rules = rule_language.rules.lock().unwrap();

        let expected_results = vec![
            (None, "(Num 31415926)", "(Num 1111)"),
            (Some("(Eq (Num 1) (Num 1))"), "(Num 31415926)", "(Num 1111)"),
        ];

        assert_eq!(rules.len(), expected_results.len());
        for (rule, (expected_condition, expected_lhs, expected_rhs)) in
            rules.iter().zip(expected_results.iter())
        {
            let (condition, lhs_val, rhs_val) = rule;
            match condition {
                None => assert!(expected_condition.is_none()),
                Some(condition) => {
                    assert!(expected_condition.is_some());
                    let expected_condition = expected_condition.as_ref().unwrap();
                    let (termdag, term) = egraph.extract_value(condition.clone());
                    assert_eq!(
                        termdag.term_to_expr(&term).to_sexp().to_string(),
                        expected_condition.to_string()
                    );
                }
            };
            let (lhs_termdag, lhs_term) = egraph.extract_value(lhs_val.clone());
            let (rhs_termdag, rhs_term) = egraph.extract_value(rhs_val.clone());
            assert_eq!(
                lhs_termdag.term_to_expr(&lhs_term).to_sexp().to_string(),
                expected_lhs.to_string()
            );
            assert_eq!(
                rhs_termdag.term_to_expr(&rhs_term).to_sexp().to_string(),
                expected_rhs.to_string()
            );
        }
    }
}
