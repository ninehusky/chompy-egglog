use crate::language::MathLang;
use crate::PredicateInterpreter;
use std::fmt::Debug;
use std::{fmt::Display, str::FromStr, sync::Arc};

use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};

use crate::{
    ite::DummySort,
    language::{CVec, ChompyLanguage, ValidationResult},
};
use egglog::{sort::EqSort, EGraph};
use log::info;
use ruler::{
    enumo::{Filter, Metric, Sexp},
    HashMap, HashSet,
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
    type Constant: Display + Debug + Clone + PartialEq;
    fn get_language(&self) -> Box<impl ChompyLanguage<Constant = Self::Constant>>;

    fn make_pred_interpreter() -> impl PredicateInterpreter + 'static;

    /// Returns the initial e-graph for the chomper, i.e.,
    /// the e-graph with the initial language definitions given from
    /// `get_language()`.
    fn get_initial_egraph(&self) -> EGraph {
        let mut egraph = EGraph::default();
        let sort = Arc::new(EqSort {
            name: self.get_language().get_name().into(),
        });

        let interp: Arc<dyn PredicateInterpreter> = Arc::new(Self::make_pred_interpreter());

        let dummy_sort = Arc::new(DummySort {
            sort: sort.clone(),
            interp,
        });

        egraph.add_arcsort(dummy_sort.clone()).unwrap();
        egraph.add_arcsort(sort.clone()).unwrap();
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
            let term1 = eclass_term_map.get(ec1).unwrap();
            let cvec1 = self.get_language().eval(term1, env);
            for ec2 in ec_keys.iter().skip(i + 1) {
                let term2 = eclass_term_map.get(ec2).unwrap();
                let cvec2 = self.get_language().eval(term2, env);
                if cvec1 == cvec2 {
                    // we add (l ~> r) and (r ~> l) as candidate rules, because
                    // we don't know which ordering is "sound" according to
                    // variable binding -- see `all_variables_bound`.
                    candidate_rules.push(Rule {
                        condition: None,
                        lhs: term1.clone(),
                        rhs: term2.clone(),
                    });
                    candidate_rules.push(Rule {
                        condition: None,
                        lhs: term2.clone(),
                        rhs: term1.clone(),
                    });
                } else {
                    let mask = cvec1
                        .iter()
                        .zip(cvec2.iter())
                        .map(|(a, b)| a == b)
                        .collect::<Vec<bool>>();
                    // if they never match, we can't generate a rule.
                    if mask.iter().all(|x| *x) {
                        panic!("cvec1 != cvec2, yet we have a mask of all true");
                    }
                    if mask.iter().all(|x| !x) {
                        continue;
                    }

                    if let Some(preds) = predicate_map.get(&mask) {
                        for pred in preds {
                            candidate_rules.push(Rule {
                                condition: Some(pred.clone()),
                                lhs: term1.clone(),
                                rhs: term2.clone(),
                            });
                            candidate_rules.push(Rule {
                                condition: Some(pred.clone()),
                                lhs: term2.clone(),
                                rhs: term1.clone(),
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

    /// Returns if the given rule can be derived from the ruleset within the given e-graph.
    /// Assumes that `rule` has been generalized (see `ChompyLanguage::generalize_rule`).
    fn rule_is_derivable(
        &self,
        initial_egraph: &EGraph,
        rule: &Rule,
        env_cache: &mut HashMap<(String, String), Vec<HashMap<String, Sexp>>>,
    ) -> bool {
        info!("assessing rule: {}", rule);

        // terms is a vector of (lhs, rhs) pairs with NO variables--not even 1...
        let terms: Vec<(Sexp, Sexp)> = self.get_language().concretize_rule(rule, env_cache);
        const MAX_DERIVABILITY_ITERATIONS: usize = 7;
        for (lhs, rhs) in terms {
            let mut egraph = initial_egraph.clone();
            self.add_term(&lhs, &mut egraph, None);
            self.add_term(&rhs, &mut egraph, None);
            let l_sexpr = format_sexp(&lhs);
            let r_sexpr = format_sexp(&rhs);
            self.run_rewrites(&mut egraph, Some(MAX_DERIVABILITY_ITERATIONS));
            // self.run_rewrites(&mut egraph, None);
            let result =
                egraph.parse_and_run_program(None, &format!("(check (= {l_sexpr} {r_sexpr}))"));
            if result.is_ok() {
                // the existing ruleset was able to derive the equality.
                return true;
            }
        }
        // the existing ruleset failed to derive the equality on all the given examples.
        false
    }

    fn add_rewrite(&self, egraph: &mut EGraph, rule: &Rule) {
        let lhs = format_sexp(&rule.lhs);
        let rhs = format_sexp(&rule.rhs);
        let prog = match &rule.condition {
            None => {
                format!(
                    r#"
                    (rule
                      (({UNIVERSAL_RELATION} {lhs}))
                      (({UNIVERSAL_RELATION} {rhs})
                       (union {lhs} {rhs}))
                      :ruleset non-cond-rewrites)
                    "#
                )
            }
            Some(cond) => {
                let cond = format_sexp(cond);
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

    fn get_pvecs(
        &self,
        env: &HashMap<String, CVec<dyn ChompyLanguage<Constant = Self::Constant>>>,
    ) -> HashMap<Vec<bool>, Vec<Sexp>> {
        let predicates = self.get_language().get_predicates();
        let mut result: HashMap<Vec<bool>, Vec<Sexp>> = Default::default();
        for p in predicates.force() {
            let vec = self
                .get_language()
                .eval(&p, env)
                .into_iter()
                .map(|val| {
                    if let Some(val) = val {
                        // TODO: check if this idea is sound: if a condition evaluates to "none", then we default to
                        // saying that the condition is false.
                        self.get_language().const_to_bool(val)
                    } else {
                        false
                    }
                })
                .collect();
            result.entry(vec).or_default().push(p);
        }
        result
    }

    fn run_chompy(&self, max_size: usize) -> Vec<Rule> {
        const MAX_ECLASS_ID: usize = 6000;
        let mut egraph = self.get_initial_egraph();

        let env = self.initialize_env();
        let env_cache = &mut HashMap::default();
        let language = self.get_language();
        let mut rules: Vec<Rule> = vec![];
        let atoms = language.base_atoms();
        let pvecs = self.get_pvecs(&env);
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
                self.add_term(term, &mut egraph, Some(max_eclass_id));
                max_eclass_id += 1;
                if max_eclass_id > MAX_ECLASS_ID {
                    panic!("max eclass id reached");
                }
            }
            if !new_workload.force().is_empty() {
                old_workload = new_workload;
            }
            let mut seen_rules: HashSet<String> = Default::default();
            loop {
                println!("running rewrites...");
                self.run_rewrites(&mut egraph, None);
                println!("i'm done running rewrites");

                let candidates = self
                    .cvec_match(&mut egraph, &pvecs, &env)
                    .into_iter()
                    .filter(all_variables_bound)
                    .collect::<Vec<Rule>>();
                if candidates.is_empty()
                    || candidates
                        .iter()
                        .all(|rule| seen_rules.contains(&rule.to_string()))
                {
                    break;
                }
                seen_rules.extend(candidates.iter().map(|rule| rule.to_string()));
                let mut just_rewrite_egraph = self.get_initial_egraph();
                for rule in rules.iter() {
                    self.add_rewrite(&mut just_rewrite_egraph, rule);
                }
                for rule in &candidates[..] {
                    let valid = language.validate_rule(rule);
                    let rule = language.generalize_rule(&rule.clone());
                    let derivable = self.rule_is_derivable(&just_rewrite_egraph, &rule, env_cache);
                    info!("candidate rule: {}", rule);
                    info!("validation result: {:?}", valid);
                    info!("is derivable? {}", if derivable { "yes" } else { "no" });
                    if valid == ValidationResult::Valid && !derivable {
                        let rule = language.generalize_rule(&rule.clone());
                        println!("rule: {}", rule);
                        rules.push(rule.clone());
                        self.add_rewrite(&mut egraph, &rule);
                        self.add_rewrite(&mut just_rewrite_egraph, &rule);
                    }
                }
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

/// A rule is "good" if the variables on the right hand side are all "bound" by the left hand
/// side.
/// A conditional rule is "good" if the above is met, and the condition only refers to variables bound by the left hand
/// side.
/// ```
/// use ruler::enumo::Sexp;
/// use std::str::FromStr;
/// use chompy::chomper::Rule;
/// use chompy::chomper::all_variables_bound;
///
/// let rule1 = Rule {
///     condition: None,
///     lhs: Sexp::from_str("(Var x)").unwrap(),
///     rhs: Sexp::from_str("(Var y)").unwrap(),
/// };
///
/// let rule2 = Rule {
///     condition: None,
///     lhs: Sexp::from_str("(Var x)").unwrap(),
///     rhs: Sexp::from_str("(Const 1)").unwrap(),
/// };
///
/// let rule3 = Rule {
///     condition: Some(Sexp::from_str("(Var y)").unwrap()),
///     lhs: Sexp::from_str("(Var x)").unwrap(),
///     rhs: Sexp::from_str("(Const 1)").unwrap(),
/// };
///
/// assert!(!all_variables_bound(&rule1));
/// assert!(all_variables_bound(&rule2));
/// assert!(!all_variables_bound(&rule3));
///     
/// ```
pub fn all_variables_bound(rule: &Rule) -> bool {
    fn get_vars(sexp: &Sexp) -> Vec<String> {
        match sexp {
            Sexp::Atom(_) => vec![],
            Sexp::List(l) => {
                if let Sexp::Atom(op) = &l[0] {
                    match op.as_str() {
                        "Var" => vec![l[1].to_string()],
                        _ => l.iter().flat_map(get_vars).collect(),
                    }
                } else {
                    panic!("Unexpected list operator: {:?}", l[0]);
                }
            }
        }
    }

    let lhs_vars = get_vars(&rule.lhs);

    // we don't want to allow rules with no variables on the left hand side.
    if lhs_vars.is_empty() {
        return false;
    }

    let rhs_vars = get_vars(&rule.rhs);
    let cond_vars = match &rule.condition {
        None => vec![],
        Some(cond) => get_vars(cond),
    };
    // rhs_vars union cond_vars must be a subset of lhs_vars.
    if rhs_vars.is_empty() && cond_vars.is_empty() {
        return true;
    }

    rhs_vars
        .iter()
        .chain(cond_vars.iter())
        .all(|var| lhs_vars.contains(var))
}

/// A sample implementation of the Chomper trait for the MathLang language.
pub struct MathChomper;

impl Chomper for MathChomper {
    type Constant = i64;

    fn make_pred_interpreter() -> impl crate::PredicateInterpreter {
        #[derive(Debug)]
        struct DummyPredicateInterpreter;
        impl PredicateInterpreter for DummyPredicateInterpreter {
            fn interp_cond(&self, sexp: &ruler::enumo::Sexp) -> bool {
                let dummy_term = MathLang::Var("dummy".to_string());
                match dummy_term.eval(sexp, &Default::default()).first().unwrap() {
                    Some(val) => *val > 0,
                    None => false,
                }
            }
        }
        DummyPredicateInterpreter
    }

    fn initialize_env(
        &self,
    ) -> ruler::HashMap<String, CVec<dyn ChompyLanguage<Constant = Self::Constant>>> {
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
