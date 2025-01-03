use std::{fmt::Display, str::FromStr, sync::Arc};

use crate::language::{CVec, ChompyLanguage, MathLang, ValidationResult};
use egglog::{sort::EqSort, EGraph};
use log::info;
use ruler::{
    enumo::{Filter, Metric, Sexp},
    HashMap,
};

const UNIVERSAL_RELATION: &str = "universe";

#[derive(Debug, Clone)]
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
    type Constant: Display + Clone + PartialEq;
    fn get_language(&self) -> Box<impl ChompyLanguage<Constant = Self::Constant>>;

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

    /// Runs the existing set of `non-cond-rewrites` and `cond-rewrites` in the e-graph
    /// for the given number of iterations. If no number of iterations is given, the rewrites
    /// are run until saturation.
    fn run_rewrites(&self, egraph: &mut EGraph, iters: Option<usize>) {
        let prog = if let Some(limit) = iters {
            format!(
                r#"
                (run-schedule
                    (repeat {limit}
                        (run non-cond-rewrites)
                        (run cond-rewrites)))
                "#
            )
            .to_string()
        } else {
            r#"
                (run-schedule
                    (saturate non-cond-rewrites)
                    (saturate cond-rewrites))
                "#
            .to_string()
        };
        egraph.parse_and_run_program(None, &prog).unwrap();
    }

    /// Returns a map from e-class id to a candidate term in the e-class.
    fn get_eclass_term_map(&self, egraph: &mut EGraph) -> HashMap<usize, Sexp> {
        let eclass_report_prog = r#"
            (push)
            (run-schedule
                (saturate eclass-report))
            (pop)
        "#;
        let mut outputs = egraph
            .parse_and_run_program(None, eclass_report_prog)
            .unwrap()
            .into_iter()
            .peekable();
        let mut eclass_term_map = HashMap::default();
        while outputs.peek().is_some() {
            outputs.next().unwrap();
            let eclass = outputs.next().unwrap().to_string().parse::<i64>().unwrap();
            outputs.next().unwrap();
            let term = Sexp::from_str(&outputs.next().unwrap()).unwrap();
            eclass_term_map.insert(eclass.try_into().unwrap(), term);
        }
        eclass_term_map
    }

    /// Returns a vector of candidate rules between e-classes in the e-graph.
    fn cvec_match(
        &self,
        egraph: &mut EGraph,
        predicate_map: &HashMap<Vec<bool>, Vec<Sexp>>,
        env: &HashMap<String, CVec<dyn ChompyLanguage<Constant = Self::Constant>>>,
    ) -> Vec<Rule> {
        let eclass_term_map = self.get_eclass_term_map(egraph);
        let mut candidate_rules = vec![];
        let ec_keys: Vec<&usize> = eclass_term_map.keys().collect();

        for i in 0..ec_keys.len() {
            let ec1 = ec_keys[i];
            let term1 = eclass_term_map.get(&ec1).unwrap();
            let cvec1 = self.get_language().eval(&term1, &env);
            for ec2 in ec_keys.iter().skip(i + 1) {
                let term2 = eclass_term_map.get(ec2).unwrap();
                let cvec2 = self.get_language().eval(&term2, &env);
                if cvec1 == cvec2 {
                    candidate_rules.push(Rule {
                        condition: None,
                        lhs: term1.clone(),
                        rhs: term2.clone(),
                    });
                } else {
                    let mask = cvec1
                        .iter()
                        .zip(cvec2.iter())
                        .map(|(a, b)| a == b)
                        .collect::<Vec<bool>>();
                    if let Some(preds) = predicate_map.get(&mask) {
                        for pred in preds {
                            candidate_rules.push(Rule {
                                condition: Some(pred.clone()),
                                lhs: term1.clone(),
                                rhs: term2.clone(),
                            });
                        }
                    }
                }
            }
        }
        candidate_rules
    }

    /// Returns a map from variable names to their values.
    fn initialize_env(
        &self,
    ) -> HashMap<String, CVec<dyn ChompyLanguage<Constant = Self::Constant>>>;

    fn rule_is_derivable(&self, initial_egraph: &EGraph, ruleset: &Vec<Rule>, rule: &Rule) -> bool {
        // terms is a vector of (lhs, rhs) pairs with NO variables--not even 1...
        let terms: Vec<(Sexp, Sexp)> = self.get_language().concretize_rule(rule);
        const MAX_DERIVABILITY_ITERATIONS: usize = 7;
        for (lhs, rhs) in terms {
            let mut egraph = initial_egraph.clone();
            self.add_term(&lhs, &mut egraph, None);
            self.add_term(&rhs, &mut egraph, None);
            self.run_rewrites(&mut egraph, Some(MAX_DERIVABILITY_ITERATIONS));
            let l_sexpr = format_sexp(&lhs);
            let r_sexpr = format_sexp(&rhs);
            let result = egraph.parse_and_run_program(None, "(check (= {l_sexpr} {r_sexpr}))");
            if !result.is_ok() {
                return false;
            }
        }
        true
    }

    fn add_rewrite(&self, egraph: &mut EGraph, rule: &Rule) {
        let lhs = format_sexp(&rule.lhs);
        let rhs = format_sexp(&rule.rhs);
        let prog = match &rule.condition {
            None => {
                format!(
                    r#"
                    (rule
                      ({lhs})
                      (({UNIVERSAL_RELATION} {lhs})
                       ({UNIVERSAL_RELATION} {rhs})
                       (union {lhs} {rhs}))
                      :ruleset non-cond-rewrites)
                    "#
                )
            }
            Some(cond) => {
                let cond = format_sexp(&cond);
                format!(
                    r#"
                    (rule
                      (({UNIVERSAL_RELATION} {lhs}))
                      ((let temp (ite {cond} {rhs} {lhs}))
                       ({UNIVERSAL_RELATION} temp)
                       (union {lhs} temp))
                      :ruleset cond-rewrites)
                    "#
                )
            }
        };
        egraph.parse_and_run_program(None, &prog).unwrap();
    }

    fn run_chompy(&self, max_size: usize) -> Vec<Rule> {
        const MAX_ECLASS_ID: usize = 1000;
        let mut egraph = self.get_initial_egraph();
        let initial_egraph = egraph.clone();
        let env = self.initialize_env();
        let language = self.get_language();
        let mut rules: Vec<Rule> = vec![];
        let atoms = language.base_atoms();
        for term in atoms.force() {
            self.add_term(&term, &mut egraph, None);
        }
        let mut old_workload = atoms.clone();
        let mut max_eclass_id: usize = 1;
        for size in 1..=max_size {
            info!("size: {}", size);
            let new_workload = atoms.clone().append(
                language
                    .produce(&old_workload.clone())
                    .filter(Filter::MetricEq(Metric::Atoms, size)),
            );
            info!("workload len: {}", new_workload.force().len());
            for term in &new_workload.force() {
                info!("term: {}", term);
                self.add_term(term, &mut egraph, Some(max_eclass_id));
                max_eclass_id += 1;
                if max_eclass_id > MAX_ECLASS_ID {
                    panic!("max eclass id reached");
                }
            }
            if !new_workload.force().is_empty() {
                old_workload = new_workload;
            }
            println!("running rewrites...");
            self.run_rewrites(&mut egraph, None);
            println!("i'm done running rewrites");

            // TODO: fix mii.
            let candidates = self.cvec_match(&mut egraph, &Default::default(), &env);
            let mut rules_at_size: Vec<Rule> = vec![];
            for rule in &candidates[..] {
                if language.validate_rule(&rule) == ValidationResult::Valid
                    && !self.rule_is_derivable(&initial_egraph, &rules, &rule)
                {
                    rules_at_size.push(rule.clone());
                    self.add_rewrite(&mut egraph, rule);
                }
            }
            println!("rules at size {}:", size);
            for rule in &rules_at_size {
                println!("{}", rule);
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

    use rand::rngs::StdRng;
    use rand::{Rng, SeedableRng};

    #[test]
    fn test_chomper() {
        struct MathChomper;

        impl Chomper for MathChomper {
            type Constant = i64;

            fn initialize_env(
                &self,
            ) -> ruler::HashMap<String, CVec<dyn ChompyLanguage<Constant = Self::Constant>>>
            {
                let mut env = ruler::HashMap::default();
                // make seedable rng
                let seed = 0b1001;
                // TODO: this should be part of the interface for eval?
                let cvec_len = 10;
                let mut rng = StdRng::seed_from_u64(seed);

                for var in self.get_language().get_vars() {
                    let cvec = (0..cvec_len)
                        .map(|_| Some(rng.gen_range(-10..10)))
                        .collect::<CVec<MathLang>>();
                    env.insert(var.clone(), cvec);
                }
                env
            }

            fn get_language(&self) -> Box<impl ChompyLanguage<Constant = Self::Constant>> {
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
