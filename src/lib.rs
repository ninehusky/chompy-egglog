use egglog::{EGraph, SerializeConfig};
use indexmap::{Equivalent, IndexSet};
use ruler::enumo::{Filter, Metric, Pattern};
use ruler::{HashMap, HashSet, ValidationResult};
use utils::{TERM_PLACEHOLDER, UNIVERSAL_RELATION};

use std::fmt::Debug;
use std::hash::Hash;
use std::str::FromStr;

use log::info;
use ruler::enumo::{Sexp, Workload};

pub mod ite;
pub mod utils;

pub type Constant<R> = <R as Chomper>::Constant;
pub type CVec<R> = Vec<Option<<R as Chomper>::Constant>>;
pub type Value<R> = <R as Chomper>::Value;

#[derive(Debug, PartialEq)]
pub struct Rule {
    pub condition: Option<Sexp>,
    pub lhs: Sexp,
    pub rhs: Sexp,
}

pub struct Rules {
    pub non_conditional: Vec<Rule>,
    pub conditional: Vec<Rule>,
}

#[derive(Debug)]
pub enum Derivability {
    Derivable,
    NotDerivable,
}

pub const MAX_SIZE: usize = 30;

#[macro_export]
macro_rules! init_egraph {
    ($egraph:ident, $path:expr) => {
        $egraph
            .parse_and_run_program(Some($path.to_string()), include_str!($path))
            .unwrap();
    };
}
pub trait Chomper {
    type Constant: Debug + Clone + Eq + Hash;
    type Value: Debug + Clone + Eq + Hash;

    // stupid. see #2.
    fn make_string_not_bad(&self, term: &str) -> String {
        let mut term_string = term.to_string();
        for var in self.get_env().keys() {
            term_string = term_string.replace(&format!(" {} ", var), &format!(" \"{}\" ", var));
        }
        term_string
    }

    fn replace_vars(&self, term: &str) -> String {
        // separate term by whitespace.
        let tokens = term.split_whitespace().collect::<Vec<_>>();
        let mut result = String::new();
        for token in tokens {
            if token.starts_with("?") {
                result += format!(" \"{}\" ", token).as_str();
            } else {
                result += format!(" {token} ").as_str();
            }
        }
        String::from(result)
    }

    fn make_mask_to_preds(&mut self) -> HashMap<Vec<bool>, HashSet<String>> {
        let mut result = HashMap::default();
        let preds = self.make_preds();
        for pred in preds.force() {
            let mask = self.interpret_pred(&pred);
            result
                .entry(mask)
                .or_insert(HashSet::default())
                .insert(pred.to_string());
        }
        result
    }

    fn run_chompy(&mut self, egraph: &mut EGraph) {
        // TODO: i want to use a set here.
        let mut found_rules: Vec<Rule> = vec![];
        let mut max_eclass_id = 0;

        let initial_egraph = egraph.clone();

        let mut non_conditional_rules: Vec<Rule> = vec![];
        let mut conditional_rules: Vec<Rule> = vec![];

        for current_size in 0..MAX_SIZE {
            println!("\n\nadding programs of size {}:", current_size);

            println!("finding eclass term map...");
            let eclass_term_map = self
                .reset_eclass_term_map(egraph)
                .values()
                .cloned()
                .collect::<Vec<_>>();
            let term_workload = Workload::new(
                eclass_term_map
                    .iter()
                    .map(|x| x.to_string())
                    .collect::<Vec<_>>(),
            );

            println!("eclasses len: {}", eclass_term_map.len());

            let new_workload = if term_workload.force().is_empty() {
                self.atoms().clone()
            } else {
                self.productions()
                    .clone()
                    .plug(TERM_PLACEHOLDER, &term_workload)
                    .filter(Filter::And(vec![
                        Filter::Canon(vec!["(Var a)".to_string(), "(Var b)".to_string()]),
                        Filter::MetricEq(Metric::Atoms, current_size),
                    ]))
            };

            println!("new workload len: {}", new_workload.force().len());

            let atoms = self.atoms().force();

            let memo = &mut HashSet::default();

            let mut id_to_gen_id: HashMap<String, String> = HashMap::default();

            let mut seen_terms: HashSet<String> = HashSet::default();

            for term in &new_workload.force() {
                let generalized = self.generalize_sexp(term.clone(), &mut id_to_gen_id);

                seen_terms.insert(generalized.to_string());

                let term_string = self.make_string_not_bad(term.to_string().as_str());

                if !atoms.contains(term) && !self.has_var(term) {
                    continue;
                }

                egraph
                    .parse_and_run_program(
                        None,
                        format!(
                            r#"
                        {term_string}
                        (set (eclass {term_string}) {max_eclass_id})
                        "#
                        )
                        .as_str(),
                    )
                    .unwrap();
                max_eclass_id += 1;
            }

            loop {
                egraph
                    .parse_and_run_program(
                        None,
                        r#"
                        (run-schedule
                            (run non-cond-rewrites))
                    "#,
                    )
                    .unwrap();
                println!("starting cvec match");
                let vals = self.cvec_match(egraph, memo);

                if vals.non_conditional.is_empty() && vals.conditional.is_empty() {
                    break;
                }

                println!("found {} non-conditional rules", vals.non_conditional.len());
                println!("found {} conditional rules", vals.conditional.len());
                // for val in &vals.conditional {
                //     let generalized = self.generalize_rule(val);
                //     if let ValidationResult::Valid = self.validate_rule(&generalized) {
                //         if utils::does_rule_have_good_vars(&generalized) {
                //             println!(
                //                 "Conditional rule: if {} then {} ~> {}",
                //                 generalized.condition.clone().unwrap(),
                //                 generalized.lhs,
                //                 generalized.rhs
                //             );

                //             if found_rules.contains(&generalized) {
                //                 continue;
                //             }
                //             let rule = Rule {
                //                 condition: generalized.condition.clone(),
                //                 lhs: generalized.lhs.clone(),
                //                 rhs: generalized.rhs.clone(),
                //             };
                //             found_rules.push(rule);
                //             self.add_conditional_rewrite(egraph, &generalized);
                //         }
                //     }
                // }

                let mut new_rules: Vec<String> = vec![];
                for val in &vals.non_conditional {
                    let generalized = self.generalize_rule(val);
                    if let ValidationResult::Valid = self.validate_rule(&generalized) {
                        if utils::does_rule_have_good_vars(&generalized) {
                            let lhs =
                                self.make_string_not_bad(generalized.lhs.to_string().as_str());
                            let rhs =
                                self.make_string_not_bad(generalized.rhs.to_string().as_str());

                            // if egraph
                            //     .parse_and_run_program(
                            //         None,
                            //         format!(r#"(check (= {} {}))"#, val.lhs, val.rhs).as_str(),
                            //     )
                            //     .is_ok()
                            // {
                            //     println!("skipping {} ~> {}", lhs, rhs);
                            //     continue;
                            // }

                            if found_rules.contains(&generalized) {
                                continue;
                            }

                            if !self.check_derivability(&initial_egraph, &found_rules, &generalized)
                            {
                                let rule = Rule {
                                    condition: generalized.condition.clone(),
                                    lhs: generalized.lhs.clone(),
                                    rhs: generalized.rhs.clone(),
                                };
                                found_rules.push(rule);
                                println!("Rule: {} ~> {}", lhs, rhs);
                                self.add_rewrite(egraph, &generalized);
                                new_rules.push(format!("{} ~> {}", lhs, rhs));
                            } else {
                                // panic!("rule was derivable");
                            }
                        }
                    } else {
                        // println!(
                        //     "perfect cvec match but failed validation: {} ~> {}",
                        //     val.lhs, val.rhs
                        // );
                    }
                }

                if new_rules.is_empty() {
                    break;
                }
            }
        }

        panic!("not all rules were found");
    }

    fn make_var(&self, var: &str) -> Sexp;

    fn concretize_term(&self, term: &Sexp, env: &mut HashMap<String, Sexp>) -> Sexp {
        match term {
            Sexp::Atom(a) => {
                if !a.starts_with("?") {
                    return Sexp::Atom(a.clone());
                }
                let new_term = self.make_var(a);
                if env.contains_key(&a.clone()) {
                    return env[&a.clone()].clone();
                }
                env.insert(a.clone(), new_term.clone());
                new_term
            }
            Sexp::List(l) => Sexp::List(l.iter().map(|x| self.concretize_term(x, env)).collect()),
        }
    }

    fn concretize_rule(&self, rule: &Rule) -> (Sexp, Sexp) {
        match rule.condition {
            Some(_) => panic!(),
            None => {
                // replace all variables with some arbitrary variable.
                let mut env = HashMap::default();
                let lhs = self.concretize_term(&rule.lhs, &mut env);
                let rhs = self.concretize_term(&rule.rhs, &mut env);
                (lhs, rhs)
            }
        }
    }

    // Returns if the rule is derivable; i.e., it shouldn't be added.
    fn check_derivability(
        &mut self,
        initial_egraph: &EGraph,
        ruleset: &Vec<Rule>,
        rule: &Rule,
    ) -> bool {
        let mut initial_egraph = initial_egraph.clone();
        for rule in ruleset {
            if rule.condition.is_some() {
                self.add_conditional_rewrite(&mut initial_egraph, &rule);
            } else {
                self.add_rewrite(&mut initial_egraph, &rule);
            }
        }
        let (lhs, rhs) = self.concretize_rule(rule);
        match &rule.condition {
            Some(_) => panic!(),
            None => {
                initial_egraph
                    .parse_and_run_program(
                        None,
                        format!(
                            r#"
                    (let lhs {})
                    (let rhs {})
                    "#,
                            self.replace_vars(lhs.to_string().as_str()),
                            self.replace_vars(rhs.to_string().as_str())
                        )
                        .as_str(),
                    )
                    .unwrap();

                initial_egraph
                    .parse_and_run_program(
                        None,
                        r#"
                        (run-schedule
                            (run non-cond-rewrites)
                            (run cond-rewrites))
                    "#,
                    )
                    .unwrap();

                let status = initial_egraph.parse_and_run_program(
                    None,
                    r#"
                    (check (= lhs rhs))
                    "#,
                );
                if status.is_err() {
                    return false;
                } else {
                    println!("skipping {} ~> {}", lhs, rhs);
                }
                true
            }
        }
    }

    fn generalize_sexp(&self, sexp: Sexp, id_to_gen_id: &mut HashMap<String, String>) -> Sexp {
        if self.matches_var_pattern(&sexp) {
            let var_name = sexp.to_string();
            let len = id_to_gen_id.len();
            id_to_gen_id
                .entry(var_name.clone())
                .or_insert_with(|| ruler::letter(len).to_string());
            return Sexp::Atom(format!("?{}", id_to_gen_id[&var_name]));
        }
        match sexp {
            Sexp::Atom(atom) => Sexp::Atom(atom),
            Sexp::List(list) => {
                let mut els = vec![];
                for el in list {
                    els.push(self.generalize_sexp(el, id_to_gen_id));
                }
                Sexp::List(els)
            }
        }
    }

    fn generalize_rule(&self, rule: &Rule) -> Rule {
        let mut id_to_gen_id: HashMap<String, String> = HashMap::default();
        let new_lhs = self.generalize_sexp(rule.lhs.clone(), &mut id_to_gen_id);
        let new_rhs = self.generalize_sexp(rule.rhs.clone(), &mut id_to_gen_id);

        let condition = rule
            .condition
            .as_ref()
            .map(|cond| self.generalize_sexp(cond.clone(), &mut id_to_gen_id));

        Rule {
            // TODO: later
            condition,
            lhs: new_lhs,
            rhs: new_rhs,
        }
    }

    fn reset_eclass_term_map(&self, egraph: &mut EGraph) -> HashMap<i64, Sexp> {
        let mut outputs = egraph
            .parse_and_run_program(
                None,
                r#"
                (push)
                (run eclass-report 100)
                (pop)"#,
            )
            .unwrap()
            .into_iter()
            .peekable();

        let mut map = HashMap::default();

        while outputs.peek().is_some() {
            outputs.next().unwrap();
            let eclass = outputs.next().unwrap().to_string().parse::<i64>().unwrap();
            outputs.next().unwrap();
            let term = outputs.next().unwrap();
            map.insert(eclass, Sexp::from_str(&term).unwrap());
        }
        map
    }

    fn cvec_match(
        &mut self,
        egraph: &mut EGraph,
        // keeps track of what eclass IDs we've seen.
        memo: &mut HashSet<i64>,
    ) -> Rules {
        let mut result = Rules {
            non_conditional: vec![],
            conditional: vec![],
        };

        let mask_to_preds = self.make_mask_to_preds();

        println!("hi from cvec match");
        let eclass_term_map: HashMap<i64, Sexp> = self.reset_eclass_term_map(egraph);
        println!("eclass term map len: {}", eclass_term_map.len());
        let ec_keys: Vec<&i64> = eclass_term_map.keys().collect();
        for i in 0..ec_keys.len() {
            let ec1 = ec_keys[i];
            if memo.contains(ec1) {
                continue;
            }
            memo.insert(*ec1);
            let term1 = eclass_term_map.get(ec1).unwrap();
            let cvec1 = self.interpret_term(term1);
            if cvec1.iter().all(|x| x.is_none()) {
                // ignore cvecs which don't really matter
                continue;
            }
            for ec2 in ec_keys.iter().skip(i + 1) {
                let term2 = eclass_term_map.get(ec2).unwrap();

                let cvec2 = self.interpret_term(term2);

                if cvec2.iter().all(|x| x.is_none()) {
                    continue;
                }

                if cvec1 == cvec2 {
                    result.non_conditional.push(Rule {
                        condition: None,
                        lhs: term1.clone(),
                        rhs: term2.clone(),
                    });
                } else {
                    if egraph
                        .parse_and_run_program(
                            None,
                            format!("(check (cond-equal {term1} {term2}))").as_str(),
                        )
                        .is_ok()
                    {
                        // TODO: we're going to ignore multiple conditionals for now, there are too many.
                        continue;
                    }

                    let mut has_meaningful_diff = false;
                    let mut same_vals: Vec<bool> = vec![];

                    for (cvec_1_el, cvec_2_el) in cvec1.iter().zip(cvec2.iter()) {
                        let has_match = cvec_1_el == cvec_2_el;
                        if !has_match && cvec_1_el.is_some() || cvec_2_el.is_some() {
                            has_meaningful_diff = true;
                        }
                        same_vals.push(has_match);
                    }

                    if !has_meaningful_diff {
                        println!("no meaningful diff");
                        continue;
                    }

                    // if the mask is all false, then skip it.
                    if same_vals.iter().all(|x| !x) {
                        continue;
                    }

                    // sufficient and necessary conditions.
                    if !mask_to_preds.contains_key(&same_vals) {
                        continue;
                    }
                    let preds = mask_to_preds.get(&same_vals).unwrap();
                    for pred in preds {
                        let rule = Rule {
                            condition: Some(Sexp::from_str(pred).unwrap()),
                            lhs: term1.clone(),
                            rhs: term2.clone(),
                        };
                        result.conditional.push(rule);
                    }
                }
            }
        }
        result
    }

    fn add_rewrite(&mut self, egraph: &mut EGraph, rule: &Rule) {
        let mut term1 = self.make_string_not_bad(rule.lhs.to_string().as_str());
        let mut term2 = self.make_string_not_bad(rule.rhs.to_string().as_str());
        // TODO: deal with rewrites which are essentially "anything matches this". they are not
        // good.
        if term1 == "?a" {
            if term2 == "?a" {
                panic!();
            }
            let temp = term2;
            term2 = term1;
            term1 = temp;
        }

        egraph
            .parse_and_run_program(
                None,
                format!(
                    r#"
                    (rewrite
                        {term1}
                        {term2}
                        :ruleset non-cond-rewrites)
                    "#
                )
                .as_str(),
            )
            .unwrap();
    }

    fn add_conditional_rewrite(&mut self, egraph: &mut EGraph, rule: &Rule) {
        // TODO: @ninehusky: let's brainstorm ways to encode conditional equality with respect to a
        // specific condition (see #20).
        let cond = rule.condition.as_ref().unwrap().to_string();
        let term1 = rule.lhs.to_string();
        let term2 = rule.rhs.to_string();

        println!(
            "adding conditional rewrite: if {} then {} -> {}",
            cond, term1, term2
        );

        let cond_rewrite_prog = format!(
            r#"
            (rule
                (({UNIVERSAL_RELATION} {term1}))
                ((union {term1} (ite {cond} {term2} {term1})))
                :ruleset cond-rewrites)
        "#
        );

        // println!("cond rewrite prog: {}", cond_rewrite_prog);

        egraph
            .parse_and_run_program(None, &cond_rewrite_prog)
            .unwrap();
    }

    fn has_var(&self, term: &Sexp) -> bool {
        match term {
            Sexp::Atom(_) => self.matches_var_pattern(term),
            Sexp::List(list) => {
                for el in list {
                    if self.matches_var_pattern(el) || self.has_var(el) {
                        return true;
                    }
                }
                false
            }
        }
    }

    fn language_name() -> String;
    fn productions(&self) -> Workload;
    fn atoms(&self) -> Workload;
    fn make_preds(&self) -> Workload;
    fn get_env(&self) -> &HashMap<String, CVec<Self>>;
    fn validate_rule(&self, rule: &Rule) -> ValidationResult;
    fn interpret_term(&self, term: &ruler::enumo::Sexp) -> CVec<Self>;
    fn interpret_pred(&self, term: &ruler::enumo::Sexp) -> Vec<bool>;
    fn constant_pattern(&self) -> Pattern;
    fn matches_var_pattern(&self, term: &Sexp) -> bool;
}
