pub mod chomper;
pub mod ite;
pub mod language;


use ruler::enumo::Sexp;
use std::fmt::Debug;

/// Helper trait which helps plug in an arbitrary interpreter for the conditional rule.
pub trait PredicateInterpreter: Debug + Send + Sync {
    fn interp_cond(&self, sexp: &Sexp) -> bool;
}
