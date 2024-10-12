// use egglog::{
//     ast::{Expr, Symbol},
//     sort::{FromSort, IntoSort, Sort},
//     util::IndexMap,
//     ArcSort, Term, Value,
// };
// use std::fmt::Debug;
// use std::sync::Mutex;
//
// use crate::Cost;
//
// use super::option::OptionSort;
//
// struct ValueExpr<T: Debug> {
//     sort: CvecSort<T>,
//     expr: Expr,
// }
//
// impl ValueExpr {
//     fn interpret(&self,
//
// type Cvec<T> = Vec<Option<T>>;
//
// impl<T: Send + Debug + 'static> IntoSort for ValueExpr<T> {
//     type Sort = CvecSort<T>;
//     fn store(self, sort: &Self::Sort) -> Option<Value> {
//         let (i, _) = sort.cvecs.lock().unwrap().insert_full(self.expr);
//         Some(Value {
//             tag: sort.name,
//             bits: i as u64,
//         })
//     }
// }
//
// impl FromSort for ValueExpr {
//     type Sort = CvecSort<T>;
//     fn load(sort: &CvecSort<T>, value: &Value) -> Self {
//         let expr = sort.cvecs.lock().unwrap().get(value.bits as usize).unwrap();
//         ValueExpr { expr }
//     }
// }
//
// #[derive(Debug)]
// pub struct CvecSort<T: Debug> {
//     name: Symbol,
//     language: OptionSort,
//     pub cvecs: Mutex<IndexMap<Term, Cvec<T>>>,
// }
//
// impl<T: Send + Debug + 'static> Sort for CvecSort<T> {
//     fn name(&self) -> Symbol {
//         self.name
//     }
//
//     fn as_arc_any(
//         self: std::sync::Arc<Self>,
//     ) -> std::sync::Arc<dyn std::any::Any + Send + Sync + 'static> {
//         self
//     }
//
//     fn make_expr(&self, egraph: &egglog::EGraph, value: Value) -> (Cost, Expr) {
//         let cvec = ValueExpr::load(self, &value);
//         self.cvecs.lock().unwrap().insert(cvec.expr);
//         let cost = 1;
//         (cost, expr)
//     }
// }
