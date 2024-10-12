use egglog::{
    ast::{Expr, Span, Symbol},
    constraint::SimpleTypeConstraint,
    sort::{FromSort, IntoSort, Sort},
    ArcSort, PrimitiveLike, TypeError, TypeInfo, Value,
};

use crate::DUMMY_SPAN;
use indexmap::IndexSet;
use std::sync::{Arc, Mutex};

use crate::Cost;

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct ValueOption {
    val: Option<Value>,
}

impl Default for ValueOption {
    fn default() -> Self {
        Self { val: None }
    }
}

#[derive(Debug)]
pub struct OptionSort {
    name: Symbol,
    element: ArcSort,
    pub options: Mutex<IndexSet<Option<Value>>>,
}

impl OptionSort {
    pub fn presort_names() -> Vec<Symbol> {
        vec!["option-some".into(), "option-none".into()]
    }

    pub fn make_sort(
        typeinfo: &mut TypeInfo,
        name: Symbol,
        args: &[Expr],
    ) -> Result<ArcSort, TypeError> {
        if let [Expr::Var(span, e)] = args {
            let e = typeinfo
                .sorts
                .get(e)
                .ok_or(TypeError::UndefinedSort(*e, span.clone()))?;

            if e.is_eq_container_sort() {
                return Err(TypeError::DisallowedSort(
                    name,
                    "Options nested with other EqSort containers are not allowed".into(),
                    span.clone(),
                ));
            }

            Ok(Arc::new(Self {
                name,
                element: e.clone(),
                options: Mutex::new(IndexSet::new()),
            }))
        } else {
            panic!("Option sort must have sort as argument. Got {:?}", args)
        }
    }
}

impl Sort for OptionSort {
    fn name(&self) -> Symbol {
        self.name
    }

    fn as_arc_any(
        self: std::sync::Arc<Self>,
    ) -> std::sync::Arc<dyn std::any::Any + Send + Sync + 'static> {
        self
    }

    fn is_container_sort(&self) -> bool {
        true
    }

    fn is_eq_container_sort(&self) -> bool {
        self.element.is_eq_sort()
    }

    fn make_expr(&self, egraph: &egglog::EGraph, value: Value) -> (Cost, Expr) {
        let option = ValueOption::load(self, &value);
        match option.val {
            None => (1, Expr::Call(DUMMY_SPAN.clone(), "None".into(), vec![])),
            Some(value) => {
                self.options.lock().unwrap().insert(Some(value));
                let (cost, expr) = self.element.make_expr(egraph, value);
                (
                    cost + 1,
                    Expr::Call(DUMMY_SPAN.clone(), "Some".into(), vec![expr]),
                )
            }
        }
    }

    fn register_primitives(self: Arc<Self>, info: &mut egglog::TypeInfo) {
        info.add_primitive(OptionNone {
            name: format!("option-none").into(),
            option: self.clone(),
        });
        info.add_primitive(OptionSome {
            name: "option-some".into(),
            option: self.clone(),
        });
    }
}

impl IntoSort for ValueOption {
    type Sort = OptionSort;
    fn store(self, sort: &Self::Sort) -> Option<Value> {
        let (i, _) = sort.options.lock().unwrap().insert_full(self.val);
        Some(Value {
            tag: sort.name,
            bits: i as u64,
        })
    }
}

impl FromSort for ValueOption {
    type Sort = OptionSort;
    fn load(sort: &Self::Sort, value: &Value) -> Self {
        ValueOption {
            val: sort
                .options
                .lock()
                .unwrap()
                .get_index(value.bits as usize)
                .unwrap()
                .clone(),
        }
    }
}

struct OptionNone {
    name: Symbol,
    option: Arc<OptionSort>,
}

impl PrimitiveLike for OptionNone {
    fn name(&self) -> Symbol {
        self.name.clone()
    }

    fn get_type_constraints(&self, span: &Span) -> Box<dyn egglog::constraint::TypeConstraint> {
        SimpleTypeConstraint::new(self.name(), vec![self.option.clone()], span.clone()).into_box()
    }

    fn apply(&self, values: &[Value], _egraph: Option<&mut egglog::EGraph>) -> Option<Value> {
        assert!(values.is_empty());
        ValueOption::default().store(&self.option)
    }
}

#[derive(Debug)]
struct OptionSome {
    name: Symbol,
    option: Arc<OptionSort>,
}

impl PrimitiveLike for OptionSome {
    fn name(&self) -> Symbol {
        self.name.clone()
    }

    fn get_type_constraints(&self, span: &Span) -> Box<dyn egglog::constraint::TypeConstraint> {
        SimpleTypeConstraint::new(
            self.name(),
            vec![self.option.element.clone(), self.option.clone()],
            span.clone(),
        )
        .into_box()
    }

    fn apply(&self, values: &[Value], _egraph: Option<&mut egglog::EGraph>) -> Option<Value> {
        ValueOption {
            val: Some(values[0].clone()),
        }
        .store(&self.option)
    }
}

#[cfg(test)]
mod tests {
    use super::OptionSort;

    #[test]
    fn test_multiple_domains() {
        let mut egraph = egglog::EGraph::default();
        egraph
            .type_info
            .presorts
            .insert("Option".into(), OptionSort::make_sort);
        egraph
            .type_info
            .presort_names
            .extend(OptionSort::presort_names());

        let outputs = egraph
            .parse_and_run_program(
                None,
                r#"
                (sort OptionInt (Option i64))
                (sort OptionBool (Option bool))
                (sort OptionIntVec (Vec OptionInt))
                (sort OptionBoolVec (Vec OptionBool))
                (let expr0 (option-some 1))
                (let expr1 (option-some 2))
                (let expr2 (option-some 3))
                (let expr3 (option-some true))
                (let expr4 (option-some false))
                ;;; just see if we can construct an option-none
                (let optionvec (vec-of expr0 expr1 (option-none)))
                (check (!= expr1 expr2))
                (extract expr3)
                "#,
            )
            .unwrap();
        assert_eq!(outputs.len(), 1);
        assert_eq!(outputs[0], "(Some true)");
    }
}
