use crate::Rule;
use ruler::enumo::Sexp;

// Atoms with this name will `not` count in a production
// toward its size.
pub const TERM_PLACEHOLDER: &str = "?term";
pub const UNIVERSAL_RELATION: &str = "universe";

pub fn get_production_size(term: &Sexp) -> usize {
    get_size(term, true)
}

pub fn get_ast_size(term: &Sexp) -> usize {
    get_size(term, false)
}

pub fn does_rule_have_good_vars(rule: &Rule) -> bool {
    // get all tokens in rule.lhs that begin with ?
    let lhs_string = rule.lhs.to_string();
    let rhs_string = rule.rhs.to_string();
    let lhs_vars: Vec<&str> = lhs_string
        .split_whitespace()
        .filter(|token| token.starts_with('?'))
        .collect();

    let rhs_vars: Vec<&str> = rhs_string
        .split_whitespace()
        .filter(|token| token.starts_with('?'))
        .collect();

    // return rhs_vars is subset of lhs_vars
    rhs_vars.iter().all(|var| lhs_vars.contains(var))
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
