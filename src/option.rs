use egglog::{
    ast::{Expr, Span, SrcFile, Symbol},
    constraint::SimpleTypeConstraint,
    sort::{FromSort, IntoSort, Sort},
    ArcSort, PrimitiveLike, Value,
};

use indexmap::IndexSet;
use lazy_static::lazy_static;
use std::sync::{Arc, Mutex};

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct ValueOption {
    val: Option<Value>,
}

const DUMMY_FILENAME: &str = "internal.egg";

lazy_static! {
    pub static ref DUMMY_FILE: Arc<SrcFile> = Arc::new(SrcFile {
        name: DUMMY_FILENAME.to_string(),
        contents: None
    });
    pub static ref DUMMY_SPAN: Span = Span(DUMMY_FILE.clone(), 0, 0);
}

/// for after meeting: i think i need one type for a some, one type for a none, and a sort for
/// the option itself. but wait... i think the type inference for the some is tricky.

#[derive(Debug)]
pub struct OptionSort<T> {
    name: Symbol,
    element: T,
    pub options: Mutex<IndexSet<Option<Value>>>,
}

impl OptionSort<ArcSort> {
    #[allow(dead_code)]
    fn new(sort: ArcSort) -> Self {
        Self {
            name: format!("Option{}", sort.name()).into(),
            element: sort,
            options: IndexSet::new().into(),
        }
    }
}

impl Sort for OptionSort<ArcSort> {
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

    fn make_expr(&self, egraph: &egglog::EGraph, value: Value) -> (usize, Expr) {
        let option = ValueOption::load(self, &value);
        match option.val {
            None => (1, Expr::Call(DUMMY_SPAN.clone(), "None".into(), vec![])),
            Some(value) => {
                // put it in the indexset
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
        println!("registering option-none-{}", self.element.name());
        info.add_primitive(OptionNone {
            name: format!("option-none-{}", self.element.name()).into(),
        });
        info.add_primitive(OptionSome {
            name: "option-some".into(),
            option: self.clone(),
        });
    }
}

impl IntoSort for ValueOption {
    type Sort = OptionSort<ArcSort>;
    fn store(self, sort: &Self::Sort) -> Option<Value> {
        // clone might be expensive.
        let (i, _) = sort.options.lock().unwrap().insert_full(self.val);
        Some(Value {
            tag: sort.name,
            bits: i as u64,
        })
    }
}

impl FromSort for ValueOption {
    type Sort = OptionSort<ArcSort>;
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
}

impl PrimitiveLike for OptionNone {
    fn name(&self) -> Symbol {
        self.name.clone()
    }

    fn get_type_constraints(&self, span: &Span) -> Box<dyn egglog::constraint::TypeConstraint> {
        SimpleTypeConstraint::new(
            self.name(),
            vec![Arc::new(egglog::sort::UnitSort::new("OptionUnit".into()))],
            span.clone(),
        )
        .into_box()
    }

    fn apply(&self, values: &[Value], _egraph: Option<&mut egglog::EGraph>) -> Option<Value> {
        assert!(values.is_empty());
        ValueOption { val: None }.store(&OptionSort::new(Arc::new(egglog::sort::UnitSort::new(
            "Unit".into(),
        ))))
    }
}

#[derive(Debug)]
struct OptionSome {
    name: Symbol,
    option: Arc<OptionSort<ArcSort>>,
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
    use crate::option::*;

    #[test]
    fn test_i64_constructor() {
        let mut egraph = egglog::EGraph::default();
        egraph
            .add_arcsort(Arc::new(OptionSort::new(Arc::new(
                egglog::sort::UnitSort::new("Unit".into()),
            ))))
            .unwrap();
        egraph
            .add_arcsort(Arc::new(OptionSort::new(Arc::new(
                egglog::sort::I64Sort::new("i64".into()),
            ))))
            .unwrap();
        let outputs = egraph
            .parse_and_run_program(
                None,
                r#"
                (let expr1 (option-some 1))
                (let expr2 (option-some 1))
                (let expr3 (option-none-i64))
                (check (= expr1 expr2))
                "#,
            )
            .unwrap();
        println!("outputs are {:?}", outputs);
    }

    #[test]
    fn test_bool_constructor() {
        let mut egraph = egglog::EGraph::default();
        egraph
            .add_arcsort(Arc::new(OptionSort::new(Arc::new(
                egglog::sort::UnitSort::new("Unit".into()),
            ))))
            .unwrap();
        egraph
            .add_arcsort(Arc::new(OptionSort::new(Arc::new(
                egglog::sort::BoolSort::new("bool".into()),
            ))))
            .unwrap();
        let outputs = egraph
            .parse_and_run_program(
                None,
                r#"
                (let expr1 (option-some true))
                (let expr2 (option-some false))
                (let expr3 (option-none-bool))
                (check (!= expr1 expr2))
                "#,
            )
            .unwrap();
        println!("outputs are {:?}", outputs);
    }

    #[test]
    fn test_multiple_domains() {
        let mut egraph = egglog::EGraph::default();
        egraph
            .add_arcsort(Arc::new(OptionSort::new(Arc::new(
                egglog::sort::UnitSort::new("Unit".into()),
            ))))
            .unwrap();
        egraph
            .add_arcsort(Arc::new(OptionSort::new(Arc::new(
                egglog::sort::BoolSort::new("bool".into()),
            ))))
            .unwrap();
        egraph
            .add_arcsort(Arc::new(OptionSort::new(Arc::new(
                egglog::sort::I64Sort::new("i64".into()),
            ))))
            .unwrap();
        let outputs = egraph
            .parse_and_run_program(
                None,
                r#"
                (let expr0 (option-some 1))
                (let expr1 (option-some true))
                (let expr2 (option-some false))
                (let expr3 (option-none-i64))
                (let expr4 (option-none-bool))
                (check (!= expr1 expr2))
                ; nones are always equal.
                (check (= expr3 expr4))
                "#,
            )
            .unwrap();
        println!("outputs are {:?}", outputs);
    }
}
