use std::fmt::{Debug, Display};

use crate::rule::Rule;
use egglog::{ast::Expr, Term};

pub type CVec<T> = Vec<Option<T>>;

pub trait Runner {
    type Constant: Debug + Display;
    fn add_exprs(&mut self, terms: Vec<Expr>) -> Result<String, String>;

    fn interpret(&mut self, term: Expr) -> Result<CVec<Self::Constant>, String>;

    fn find_rules(&self, cvecs: &CVec<Self::Constant>) -> Vec<Rule>;
}
