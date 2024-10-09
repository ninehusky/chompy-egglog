use std::sync::{Arc, Mutex};

use egglog::{util::IndexMap, Term, ast::Symbol, ArcSort, sort::Sort};

/// Cvecs are vectors of some primitive type.
///
/// They should be the evaluation of
/// some term within the egraph.

#[derive(Debug)]
pub struct CvecSort<T> {
    name: Symbol,
    element: ArcSort,
    // maps canonical term -> cvec.
    memoize: Mutex<IndexMap<Term, Option<T>>>,
}


