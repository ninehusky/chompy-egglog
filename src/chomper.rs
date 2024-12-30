use std::{fmt::Display, sync::Arc};

use crate::language::ChompyLanguage;
use egglog::{sort::EqSort, EGraph};
use ruler::enumo::{Filter, Metric, Sexp};

const UNIVERSAL_RELATION: &str = "universe";

#[derive(Debug)]
pub struct Rule {
    pub condition: Option<Sexp>,
    pub lhs: Sexp,
    pub rhs: Sexp,
}

impl Display for Rule {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(cond) = &self.condition {
            write!(f, "if {} then {} ~> {}", cond, self.lhs, self.rhs)
        } else {
            write!(f, "{} ~> {}", self.lhs, self.rhs)
        }
    }
}

/// Chompers manage the state of the e-graph.
pub trait Chomper {
    type Constant: Display + Clone;
    fn get_language(&self) -> Box<dyn ChompyLanguage<Constant = Self::Constant>>;

    /// Returns the initial e-graph for the chomper, i.e.,
    /// the e-graph with the initial language definitions given from
    /// `get_language()`.
    fn get_initial_egraph(&self) -> EGraph {
        let mut egraph = EGraph::default();
        let sort = Arc::new(EqSort {
            name: self.get_language().get_name().into(),
        });
        egraph.add_arcsort(sort).unwrap();
        egraph
            .parse_and_run_program(None, &self.get_language().to_egglog_src())
            .unwrap();
        egraph
    }

    /// Adds the given term to the e-graph.
    /// Optionally, sets the eclass id of the term to the given id.
    fn add_term(&self, term: &Sexp, egraph: &mut EGraph, eclass_id: Option<usize>) {
        let term = format_sexp(term);
        let prog = format!("({} {})", UNIVERSAL_RELATION, term);
        egraph.parse_and_run_program(None, &prog).unwrap();
        if let Some(id) = eclass_id {
            egraph
                .parse_and_run_program(None, format!("(set (eclass {term}) {id})").as_str())
                .unwrap();
        }
    }

    fn run_chompy(&self, max_size: usize) -> Vec<Rule> {
        let mut egraph = self.get_initial_egraph();
        let language = self.get_language();
        let mut rules: Vec<Rule> = vec![];
        let atoms = language.base_atoms();
        for term in atoms.force() {
            self.add_term(&term, &mut egraph, None);
        }
        let mut old_workload = atoms.clone();
        let mut max_eclass_id: usize = 1;
        for size in 1..=max_size {
            println!("size: {}", size);
            let new_workload = atoms.clone().append(
                language
                    .produce(&old_workload.clone())
                    .filter(Filter::MetricEq(Metric::Atoms, size)),
            );
            println!("workload len: {}", new_workload.force().len());
            for term in &new_workload.force() {
                println!("term: {}", term);
                self.add_term(term, &mut egraph, Some(max_eclass_id));
                max_eclass_id += 1;
            }
            if !new_workload.force().is_empty() {
                old_workload = new_workload;
            }
        }
        rules
    }
}

/// Helper function which adds quotes around Var atoms in the given S-expression.
/// Adds some spaces.
/// See #3 for details on why we need this.
/// ```
/// use ruler::enumo::Sexp;
/// use std::str::FromStr;
/// use chompy::chomper::format_sexp;
/// let sexp = Sexp::from_str("(Var x)").unwrap();
/// assert_eq!(format_sexp(&sexp), "(Var \"x\" ) ");
/// ```
pub fn format_sexp(sexp: &Sexp) -> String {
    let s = sexp.to_string();
    let s = s.split_whitespace();
    let mut need_quote = false;
    let mut result = String::new();
    for token in s {
        if need_quote {
            result.push_str(&format!("\"{}\"", token));
            need_quote = false;
        } else {
            result.push_str(token);
            if token == "(Var" {
                need_quote = true;
            }
        }
        result.push(' ');
    }
    result
}

pub mod tests {
    use crate::language::MathLang;

    use crate::chomper::Chomper;
    use crate::language::*;

    #[test]
    fn test_chomper() {
        struct MathChomper;

        impl Chomper for MathChomper {
            type Constant = i64;

            fn get_language(&self) -> Box<dyn ChompyLanguage<Constant = Self::Constant>> {
                Box::new(MathLang::Var("dummy".to_string()))
            }
        }

        let chomper = MathChomper;
        let rules = chomper.run_chompy(10);
        for rule in rules {
            println!("{}", rule);
        }
    }
}
