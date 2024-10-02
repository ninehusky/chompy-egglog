use crate::language::*;

pub trait Runner<L: ChompyLang> {
    fn add_terms(&mut self, terms: Vec<L>) -> Result<String, String>;

    fn interpret(&mut self, term: L) -> Result<CVec<L>, String>;
}
