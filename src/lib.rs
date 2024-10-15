use egglog::{
    ast::{Span, DUMMY_FILE},
    EGraph,
};
use lazy_static::lazy_static;

lazy_static! {
    pub static ref DUMMY_SPAN: Span = Span(DUMMY_FILE.clone(), 0, 0);
}

type Cost = usize;
