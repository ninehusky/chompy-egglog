use ruler::enumo::Sexp;

// Atoms with this name will `not` count in a production
// toward its size.
pub const TERM_PLACEHOLDER: &str = "?term";

pub fn get_production_size(term: &Sexp) -> usize {
    get_size(&term, true)
}

pub fn get_ast_size(term: &Sexp) -> usize {
    get_size(&term, false)
}

fn get_size(term: &Sexp, skip_placeholders: bool) -> usize {
    match term {
        Sexp::Atom(atom) => {
            if skip_placeholders && atom == TERM_PLACEHOLDER {
                return 0;
            }
            1
        }
        Sexp::List(list) => {
            let mut size = 0;
            for item in list {
                size += get_size(item, skip_placeholders);
            }
            size
        }
    }
}
