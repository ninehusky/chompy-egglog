pub mod sort;

use egglog::{
    ast::{Span, DUMMY_FILE},
    EGraph,
};
use lazy_static::lazy_static;
use sort::option::OptionSort;

lazy_static! {
    pub static ref DUMMY_SPAN: Span = Span(DUMMY_FILE.clone(), 0, 0);
}

type Cost = usize;

pub fn initialize_chompy() -> EGraph {
    let mut egraph = EGraph::default();
    // TODO: egraph: initialize language
    // TODO: egraph: initialize rules that generate cvecs.
    egraph
        .type_info
        .presorts
        .insert("Option".into(), OptionSort::make_sort);
    egraph
        .type_info
        .presort_names
        .extend(OptionSort::presort_names());
    egraph
}
