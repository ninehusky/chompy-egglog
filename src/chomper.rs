use crate::cvec::CvecSort;
use crate::language::{mathlang_to_z3, MathLang};
use std::fmt::Debug;
use std::hash::{DefaultHasher, Hash, Hasher};
use std::{fmt::Display, str::FromStr, sync::Arc};

use egglog::ast::Span;
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use z3::ast::Ast;

use crate::language::{CVec, ChompyLanguage, ValidationResult};
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

    /// Returns the initial e-graph for the chomper, i.e.,
    /// the e-graph with the initial language definitions given from
    /// `get_language()`.
    fn get_initial_egraph(&self) -> EGraph {
        let mut egraph = EGraph::default();

        egraph
            .add_arcsort(Arc::new(CvecSort::new()), Span::Panic)
            .unwrap();

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
    fn add_term(&self, term: &Sexp, egraph: &mut EGraph) {
        info!("adding term: {}", term);
        let term = format_sexp(term);
        let prog = format!(
            r#"
            {term}
            (universe {term})
        "#
        );
        egraph.parse_and_run_program(None, &prog).unwrap();
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
    /// It better be the case that by the time we're calling this,
    /// that every term in the e-graph has a Cvec associated with it.
    fn cvec_match(
        &self,
        egraph: &mut EGraph,
        predicate_map: &HashMap<Vec<bool>, Vec<Sexp>>,
        // Yeah.
        cvecs: &HashMap<i64, CVec<dyn ChompyLanguage<Constant = Self::Constant>>>,
        env: &HashMap<String, CVec<dyn ChompyLanguage<Constant = Self::Constant>>>,
    ) -> Vec<Rule> {
        let find_cvec_prog = r#"
        (run-schedule
            (saturate discover-candidates))
        "#;
        let terms = egraph.parse_and_run_program(None, find_cvec_prog).unwrap();
        // TODO: let's just see what's in "terms"

        vec![]
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

        if !lhs.to_string().contains("?") && !rhs.to_string().contains("?") {
            // we don't want to assert equalities between constants.
            return true;
        }

        const MAX_DERIVABILITY_ITERATIONS: usize = 3;

        let mut egraph = initial_egraph.clone();
        self.add_term(&lhs, &mut egraph);
        self.add_term(&rhs, &mut egraph);
        println!("lhs: {}", lhs);
        println!("rhs: {}", rhs);
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

    fn assign_cvecs(
        &self,
        egraph: &mut EGraph,
        env: &HashMap<String, CVec<dyn ChompyLanguage<Constant = Self::Constant>>>,
    ) -> () {
        let get_unassigned_terms_prog = r#"
            (run-schedule
                (saturate find-no-cvec-terms))
        "#;
        let terms = egraph
            .parse_and_run_program(None, get_unassigned_terms_prog)
            .unwrap();

        let sexps = terms.iter().map(|term| Sexp::from_str(term).unwrap());

        for sexp in sexps {
            let cvec = self.get_language().eval(&sexp, &env);
            let mut hasher = DefaultHasher::new();
            cvec.hash(&mut hasher);
            let hash: u64 = hasher.finish();
            if hash == 0 {
                panic!(
                    "Can't have cvec hash of 0. We just can't. Term was: {}",
                    sexp
                );
            }
            let hash = format!("{:?}", cvec);
            let sexp = format_sexp(&sexp);
            egraph
                .parse_and_run_program(
                    None,
                    &format!("(set (HasCvecHash {sexp}) (SomeCvec \"{hash}\"))"),
                )
                .unwrap();
        }
    }

    fn get_candidates(&self, egraph: &mut EGraph) -> Vec<Rule> {
        let mut candidates: Vec<Rule> = vec![];

        println!("BEFORE");
        let size_info = egraph
            .parse_and_run_program(None, r#"(print-size)"#)
            .unwrap();
        for info in size_info {
            println!("{}", info);
        }

        let get_candidates_prog = r#"
            (run-schedule
                (saturate discover-cond-candidates)
                (saturate discover-total-candidates))

            (run-schedule
                (saturate print-candidates))
        "#;

        let found_candidates = egraph
            .parse_and_run_program(None, get_candidates_prog)
            .unwrap();

        println!("AFTER");
        let size_info = egraph
            .parse_and_run_program(None, r#"(print-size)"#)
            .unwrap();
        for info in size_info {
            println!("{}", info);
        }

        for candidate in found_candidates {
            let sexp = Sexp::from_str(&candidate).unwrap();
            if let Sexp::List(ref l) = sexp {
                match l.len() {
                    4 => {
                        assert_eq!(l[0], Sexp::Atom("ConditionalRule".to_string()));
                        candidates.push(Rule {
                            condition: Some(l[1].clone()),
                            lhs: l[2].clone(),
                            rhs: l[3].clone(),
                        });
                    }
                    3 => {
                        assert_eq!(l[0], Sexp::Atom("TotalRule".to_string()));
                        candidates.push(Rule {
                            condition: None,
                            lhs: l[1].clone(),
                            rhs: l[2].clone(),
                        });
                    }
                    _ => panic!(
                        "Unexpected length of rule sexpression {:?}: {}",
                        sexp,
                        l.len()
                    ),
                }
            } else {
                panic!("Unexpected sexp: {:?}", sexp);
            }
        }

        candidates
    }

    fn run_chompy(&self, max_size: usize) -> Vec<Rule> {
        const MAX_ECLASS_ID: usize = 6000;
        let mut egraph = self.get_initial_egraph();

        let env = self.initialize_env();
        let language = self.get_language();
        let mut rules: Vec<Rule> = vec![];
        let atoms = language.base_atoms();
        let pvecs = self.get_pvecs(&env);
        // TODO: we should remove commented out portion entirely; the idea of
        // new workload is that it should be the set union of atoms and new stuff.
        // for term in atoms.force() {
        //     self.add_term(&term, &mut egraph, None);
        // }
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
                self.add_term(term, &mut egraph);
                let sexp = format_sexp(term);
                egraph
                    .parse_and_run_program(
                        None,
                        format!("(set (HasCvecHash {sexp}) (NoneCvec))").as_str(),
                    )
                    .unwrap();

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

                println!("assigning cvecs...");
                self.assign_cvecs(&mut egraph, &env);
                println!("done assigning cvecs");

                println!("getting candidates...");
                let mut candidates = self.get_candidates(&mut egraph);
                println!("done getting candidates");

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
                    println!("candidate rule: {}", rule);
                    println!("validation result: {:?}", valid);
                    println!("is derivable? {}", if derivable { "yes" } else { "no" });
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
