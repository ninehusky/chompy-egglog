use crate::language::{mathlang_to_z3, MathLang};
use crate::PredicateInterpreter;
use std::fmt::Debug;
use std::hash::Hash;
use std::{fmt::Display, str::FromStr, sync::Arc};

use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use z3::ast::Ast;

use crate::{
    ite::DummySort,
    language::{CVec, ChompyLanguage, ValidationResult},
};
use egglog::{sort::EqSort, EGraph};
use log::info;
use ruler::{
    enumo::{Filter, Sexp},
    HashMap, HashSet,
};

const UNIVERSAL_RELATION: &str = "universe";

#[derive(Debug, Clone, PartialEq, Eq)]
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

impl Rule {
    pub fn cost(&self) -> usize {
        fn cost(sexp: &Sexp) -> usize {
            match sexp {
                Sexp::Atom(a) => {
                    // prioritize variables over other things.
                    if a == "Var" {
                        1
                    } else {
                        2
                    }
                }
                Sexp::List(l) => l.iter().map(cost).sum(),
            }
        }

        cost(&self.lhs)
            + cost(&self.rhs)
            + match &self.condition {
                None => 0,
                Some(cond) => cost(cond),
            }
    }
}

impl PartialOrd for Rule {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Rule {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.cost().cmp(&other.cost())
    }
}

/// Chompers manage the state of the e-graph.
pub trait Chomper {
    type Constant: Display + Debug + Clone + PartialEq + Hash + Eq;
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

        for implication_prog in self.predicate_implication_ruleset() {
            egraph
                .parse_and_run_program(None, &implication_prog.to_string())
                .unwrap();
        }
        egraph
    }

    /// Adds the given term to the e-graph.
    /// Optionally, sets the eclass id of the term to the given id.
    fn add_term(&self, term: &Sexp, egraph: &mut EGraph, eclass_id: Option<usize>) {
        info!("adding term: {}", term);
        let term = format_sexp(term);
        let prog = format!("({} {})", UNIVERSAL_RELATION, term);
        egraph.parse_and_run_program(None, &prog).unwrap();
        if let Some(id) = eclass_id {
            let prog = format!("(set (eclass {term}) {id})", term = term, id = id);
            info!("running program: {}", prog);
            egraph.parse_and_run_program(None, &prog).unwrap();
        }
    }

    /// Runs the existing set of `total-rewrites` and `cond-rewrites` in the e-graph
    /// for the given number of iterations. If no number of iterations is given, the rewrites
    /// are run until saturation.
    fn run_rewrites(&self, egraph: &mut EGraph, iters: Option<usize>) {
        let prog = if let Some(limit) = iters {
            format!(
                r#"
                (run-schedule
                    (repeat {limit}
                        (run total-rewrites)
                        (run cond-rewrites)))
                "#
            )
            .to_string()
        } else {
            r#"
                (run-schedule
                    (saturate total-rewrites)
                    (saturate cond-rewrites))
                "#
            .to_string()
        };

        let prog = format!("{prog}\n(print-stats)\n");

        info!("running rewrites: {}", prog);

        let results = egraph.parse_and_run_program(None, &prog).unwrap();

        log_rewrite_stats(results);
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

    fn validate_implication(&self, p1: &Sexp, p2: &Sexp) -> bool;

    /// Returns a vector of Egglog rules, i.e., Egglog programs.
    fn predicate_implication_ruleset(&self) -> Vec<String> {
        fn generalize_predicate(sexp: &Sexp, vars: Vec<String>) -> Sexp {
            match sexp {
                Sexp::Atom(a) => {
                    if vars.contains(a) {
                        Sexp::from_str(&format!("?{}", a)).unwrap()
                    } else {
                        sexp.clone()
                    }
                }
                Sexp::List(l) => Sexp::List(
                    l.iter()
                        .map(|s| generalize_predicate(s, vars.clone()))
                        .collect(),
                ),
            }
        }

        // I don't know if this is smart.
        let predicates: Vec<Sexp> = self
            .get_language()
            .get_predicates()
            .filter(Filter::Canon(self.get_language().get_vars()))
            .force();

        let mut result: Vec<String> = vec![];

        let vars = self.get_language().get_vars();

        // go pairwise
        for p in &predicates {
            for q in &predicates {
                // creating dummy rule to ensure
                if p == q
                    || !all_variables_bound(&Rule {
                        condition: None,
                        lhs: p.clone(),
                        rhs: q.clone(),
                    })
                {
                    continue;
                }

                // if p => q, then add (p -> q) to the list of implications.
                if self.validate_implication(p, q) {
                    let p = generalize_predicate(p, vars.clone());
                    let q = generalize_predicate(q, vars.clone());
                    result.push(format!(
                        r#"
(rule
    ((= (Condition {p}) (TRUE)))
    ((union (Condition {q}) (TRUE)))
    :ruleset condition-propagation)
                    "#
                    ));
                }
            }
        }
        result
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

        info!("number of e-classes: {}", ec_keys.len());

        for i in 0..ec_keys.len() {
            let ec1 = ec_keys[i];
            let term1 = eclass_term_map.get(ec1).unwrap();
            // TODO:
            // if term1 = (Const x) {
            //     continue;
            // }
            if let Sexp::List(l) = term1 {
                if l[0] == Sexp::Atom("Const".to_string()) {
                    continue;
                }
            }
            let cvec1 = self.get_language().eval(term1, env);
            // if all terms in the cvec are equal, cotinue.
            if cvec1.iter().all(|x| x == cvec1.first().unwrap()) {
                continue;
            }
            for ec2 in ec_keys.iter().skip(i + 1) {
                let term2 = eclass_term_map.get(ec2).unwrap();
                if let Sexp::List(l) = term2 {
                    if l[0] == Sexp::Atom("Const".to_string()) {
                        continue;
                    }
                }
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

                    // if under the mask, all of cvec1 is the same value, then skip.
                    let cvec1_vals_under_pred = cvec1
                        .iter()
                        .zip(mask.iter())
                        .filter(|(_, &b)| b)
                        .map(|(x, _)| x.clone())
                        .collect::<Vec<_>>();

                    let cvec2_vals_under_pred = cvec2
                        .iter()
                        .zip(mask.iter())
                        .filter(|(_, &b)| b)
                        .map(|(x, _)| x.clone())
                        .collect::<Vec<_>>();

                    // TODO: make this happen conditionally via a flag
                    // get num of unique values under the predicate.
                    let num_unique_vals =
                        cvec1_vals_under_pred.iter().collect::<HashSet<_>>().len();

                    if num_unique_vals == 1 {
                        continue;
                    }

                    let num_unique_vals =
                        cvec2_vals_under_pred.iter().collect::<HashSet<_>>().len();

                    if num_unique_vals == 1 {
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

    fn run_condition_propagation(&self, egraph: &mut EGraph, iters: Option<usize>) {
        if let Some(iters) = iters {
            egraph
                .parse_and_run_program(
                    None,
                    &format!(
                        "(run-schedule (repeat {iters} (run condition-propagation)))",
                        iters = iters
                    ),
                )
                .unwrap();
        } else {
            egraph
                .parse_and_run_program(None, "(run-schedule (saturate condition-propagation))")
                .unwrap();
        }
    }

    /// Returns if the given rule can be derived from the ruleset within the given e-graph.
    /// Assumes that `rule` has been generalized (see `ChompyLanguage::generalize_rule`).
    fn rule_is_derivable(&self, initial_egraph: &EGraph, rule: &Rule) -> bool {
        // TODO: make a cleaner implementation of below:
        if let Some(cond) = &rule.condition {
            if cond.to_string() == rule.lhs.to_string() {
                info!(
                    "skipping bad rule with bad form of if c then c ~> r : {}",
                    rule
                );
                return true;
            }
        }

        info!("assessing rule: {}", rule);

        fn simple_concretize(sexp: &Sexp) -> Sexp {
            match sexp {
                Sexp::Atom(a) => {
                    if let Some(stripped) = a.strip_prefix("?") {
                        Sexp::from_str(format!("(Var {})", stripped).as_str()).unwrap()
                    } else {
                        sexp.clone()
                    }
                }
                Sexp::List(l) => Sexp::List(l.iter().map(simple_concretize).collect()),
            }
        }

        // terms is a vector of (lhs, rhs) pairs with NO variables--not even 1...

        let lhs = simple_concretize(&rule.lhs);
        let rhs = simple_concretize(&rule.rhs);
        const MAX_DERIVABILITY_ITERATIONS: usize = 3;

        let mut egraph = initial_egraph.clone();
        self.add_term(&lhs, &mut egraph, None);
        self.add_term(&rhs, &mut egraph, None);
        if let Some(cond) = &rule.condition {
            let cond = format_sexp(&simple_concretize(cond));
            egraph
                .parse_and_run_program(None, &format!("(union (Condition {cond}) (TRUE))"))
                .unwrap();
            self.run_condition_propagation(&mut egraph, Some(MAX_DERIVABILITY_ITERATIONS));
        }
        self.run_rewrites(&mut egraph, Some(MAX_DERIVABILITY_ITERATIONS));
        let result = self.check_equality(&mut egraph, &lhs, &rhs);
        if !result {
            // the existing ruleset was unable to derive the equality.
            return false;
        }
        // the existing ruleset was able to derive the equality on all the given examples.
        true
    }

    fn check_equality(&self, egraph: &mut EGraph, lhs: &Sexp, rhs: &Sexp) -> bool {
        egraph
            .parse_and_run_program(
                None,
                &format!("(check (= {} {}))", format_sexp(lhs), format_sexp(rhs)),
            )
            .is_ok()
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
                      :ruleset total-rewrites)
                    "#
                )
            }
            Some(cond) => {
                let cond = format_sexp(cond);
                format!(
                    r#"
                    (rule
                      (({UNIVERSAL_RELATION} {lhs})
                       (= (Condition {cond}) (TRUE)))
                       ((union {lhs} {rhs}))
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
        let language = self.get_language();
        let mut rules: Vec<Rule> = vec![];
        let atoms = language.base_atoms();
        let pvecs = self.get_pvecs(&env);
        for term in atoms.force() {
            self.add_term(&term, &mut egraph, None);
        }
        let mut max_eclass_id: usize = 1;

        // chompy does not consider terms with constants as subterms after programs
        // the size exceeds a certain threshold.
        let const_threshold = 5;

        for size in 1..=max_size {
            println!("CONSIDERING PROGRAMS OF SIZE {}:", size);
            let mut new_workload = atoms.clone().append(language.produce(size));

            if size > const_threshold {
                new_workload = new_workload.filter(Filter::Excludes("Const".parse().unwrap()));
            }

            println!("workload len: {}", new_workload.force().len());
            for term in &new_workload.force() {
                self.add_term(term, &mut egraph, Some(max_eclass_id));
                max_eclass_id += 1;
                if max_eclass_id > MAX_ECLASS_ID {
                    panic!("max eclass id reached");
                }
            }
            let mut seen_rules: HashSet<String> = Default::default();
            loop {
                info!("trying to merge new terms using existing rewrites...");
                self.run_rewrites(&mut egraph, Some(7));
                info!("i'm done running rewrites");

                let mut candidates = self
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
                println!("NUM CANDIDATES: {}", candidates.len());
                seen_rules.extend(candidates.iter().map(|rule| rule.to_string()));
                let mut just_rewrite_egraph = self.get_initial_egraph();
                for rule in rules.iter() {
                    self.add_rewrite(&mut just_rewrite_egraph, rule);
                }
                candidates.sort();
                for rule in &candidates[..] {
                    let valid = language.validate_rule(rule);
                    let rule = language.generalize_rule(&rule.clone());
                    let derivable = self.rule_is_derivable(&just_rewrite_egraph, &rule);
                    info!("candidate rule: {}", rule);
                    info!("validation result: {:?}", valid);
                    info!("is derivable? {}", if derivable { "yes" } else { "no" });
                    if valid == ValidationResult::Valid && !derivable {
                        let rule = language.generalize_rule(&rule.clone());
                        info!("rule: {}", rule);
                        println!("RULE IS: {}", rule);
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

fn log_rewrite_stats(outputs: Vec<String>) {
    fn chop_off_seconds(s: &str) -> f64 {
        s.split('s').next().unwrap().parse().unwrap()
    }

    let long_time = 0.1;
    let last_two = outputs.iter().rev().take(2).collect::<Vec<&String>>();
    for line in last_two.iter().rev() {
        // the last, third to last, and fifth to last tokens are the relevant ones.
        let tokens = line.split_whitespace().collect::<Vec<&str>>();
        let rebuild_time = chop_off_seconds(tokens.last().unwrap());
        let apply_time = chop_off_seconds(tokens[tokens.len() - 3]);
        let search_time = chop_off_seconds(tokens[tokens.len() - 5]);
        if search_time > long_time || apply_time > long_time || rebuild_time > long_time {
            info!("LONG TIME");
        }
        // if search_time > long_time || apply_time > long_time || rebuild_time > long_time {
        //
        info!("Egglog output:");
        info!("{}", line);
        // }
    }
}
/// A sample implementation of the Chomper trait for the MathLang language.
pub struct MathChomper;

impl Chomper for MathChomper {
    type Constant = i64;

    fn validate_implication(&self, p1: &Sexp, p2: &Sexp) -> bool {
        // TODO: Vivien suggests using Z3's incremental mode to avoid having to tear down and
        // rebuild the context every time.
        let p1: MathLang = p1.clone().into();
        let p2: MathLang = p2.clone().into();
        let mut cfg = z3::Config::new();
        cfg.set_timeout_msec(1000);
        let ctx = z3::Context::new(&cfg);
        let solver = z3::Solver::new(&ctx);
        let p1 = mathlang_to_z3(&ctx, &p1.clone());
        let p2 = mathlang_to_z3(&ctx, &p2.clone());
        let one = z3::ast::Int::from_i64(&ctx, 1);
        let assert_prog = &z3::ast::Bool::implies(&p1._eq(&one), &p2._eq(&one));
        solver.assert(assert_prog);
        let result = solver.check();
        match result {
            z3::SatResult::Sat => true,
            z3::SatResult::Unsat => false,
            z3::SatResult::Unknown => {
                info!("Z3 could not determine the validity of the implication.");
                false
            }
        }
    }

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
