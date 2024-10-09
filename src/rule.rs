use egglog::ast::{Action, Expr};

pub struct Rule {
    name: String,
    condition: Option<Expr>,
    lhs: Expr,
    rhs: Expr,
}
