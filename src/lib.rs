use egglog::EGraph;
use ruler::{HashMap, HashSet, ValidationResult};
use utils::TERM_PLACEHOLDER;

use std::fmt::Debug;
use std::hash::Hash;
use std::str::FromStr;

use ruler::enumo::{Filter, Metric, Sexp, Workload};

use log::info;

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

    fn make_initial_corpus(&self) -> Vec<Workload> {
        let mut corpus: Vec<Vec<String>> = vec![vec![]; MAX_SIZE];
        for atom in &self.atoms().force() {
            let size = utils::get_ast_size(atom);
            corpus[size].push(atom.to_string());
        }
        corpus.into_iter().map(Workload::new).collect()
    }

    fn run_chompy(
        &mut self,
        egraph: &mut EGraph,
        _test_name: &str,
        rules: Vec<Rule>,
        _atoms: &Workload,
        mask_to_preds: &HashMap<Vec<bool>, HashSet<String>>,
    ) {
        let mut found: Vec<bool> = vec![false; rules.len()];

        let mut max_eclass_id = 0;

        // invariant: `corpus` contains all programs of size `i`.
        for current_size in 0..MAX_SIZE {
            info!("adding programs of size {}:", current_size);

            let mut filter = Filter::MetricEq(Metric::Atoms, current_size);
            if current_size > 15 {
                filter = Filter::And(vec![
                    filter,
                    Filter::Excludes("(Bitvector ?x (ValueNum ?y))".parse().unwrap()),
                ]);
            }

            info!("finding eclass term map...");
            let eclass_term_map = self
                .reset_eclass_term_map(egraph)
                .values()
                .cloned()
                .collect::<Vec<_>>();
            info!("eclass term map len: {}", eclass_term_map.len());
            let term_workload = Workload::new(
                eclass_term_map
                    .iter()
                    .map(|x| x.to_string())
                    .collect::<Vec<_>>(),
            );

            let new_workload = if term_workload.force().is_empty() {
                self.atoms().clone()
            } else {
                self.productions()
                    .clone()
                    .plug(TERM_PLACEHOLDER, &term_workload)
                    .filter(filter)
            };

            info!("new workload len: {}", new_workload.force().len());

            for term in &new_workload.force() {
                // TODO: re-include this.
                // if get_ast_size(term) < current_size {
                //     panic!();
                // }
                let term_string = self.make_string_not_bad(term.to_string().as_str());
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
                info!("starting cvec match");
                let vals = self.cvec_match(egraph, mask_to_preds);
                info!("found {} non-conditional rules", vals.non_conditional.len());
                info!("found {} conditional rules", vals.conditional.len());
                if vals.non_conditional.is_empty() {
                    break;
                }

                for (i, rule) in rules.iter().enumerate() {
                    let lhs = self.make_string_not_bad(rule.lhs.to_string().as_str());
                    let rhs = self.make_string_not_bad(rule.rhs.to_string().as_str());
                    if rule.condition.is_some()
                        && egraph
                            .parse_and_run_program(
                                None,
                                format!(
                                    r#"
                                (check (cond-equal {lhs} {rhs}))
                                "#
                                )
                                .as_str(),
                            )
                            .is_ok()
                    {
                        found[i] = true;
                    } else if egraph
                        .parse_and_run_program(
                            None,
                            format!(
                                r#"
                                {lhs}
                                {rhs}
                                (check (= {lhs} {rhs}))
                                "#
                            )
                            .as_str(),
                        )
                        .is_ok()
                    {
                        found[i] = true;
                    };
                    if found.iter().all(|x| *x) {
                        return;
                    }
                }

                for val in &vals.non_conditional {
                    let lhs = self.make_string_not_bad(val.lhs.to_string().as_str());
                    let rhs = self.make_string_not_bad(val.rhs.to_string().as_str());
                    if egraph
                        .parse_and_run_program(
                            None,
                            format!(
                                r#"
                            {lhs}
                            {rhs}
                            ; (run-schedule
                            ;     (saturate non-cond-rewrites))
                            (check (= {lhs} {rhs}))
                            "#
                            )
                            .as_str(),
                        )
                        .is_err()
                    {
                        self.add_rewrite(egraph, val.lhs.clone(), val.rhs.clone());
                    };
                }

                for val in &vals.conditional {
                    self.add_conditional_rewrite(
                        egraph,
                        val.condition.clone().unwrap(),
                        val.lhs.clone(),
                        val.rhs.clone(),
                    );
                }

                egraph
                    .parse_and_run_program(
                        None,
                        r#"
                        (run-schedule
                            (saturate non-cond-rewrites))
                    "#,
                    )
                    .unwrap();
            }
        }

        panic!("not all rules were found");
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
        mask_to_preds: &HashMap<Vec<bool>, HashSet<String>>,
    ) -> Rules {
        let mut result = Rules {
            non_conditional: vec![],
            conditional: vec![],
        };

        let eclass_term_map: HashMap<i64, Sexp> = self.reset_eclass_term_map(egraph);
        let ec_keys: Vec<&i64> = eclass_term_map.keys().collect();
        for i in 0..ec_keys.len() {
            let ec1 = ec_keys[i];
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
                    result.non_conditional.push(Rule {
                        condition: None,
                        lhs: term2.clone(),
                        rhs: term1.clone(),
                    });
                } else {
                    // TODO: we're going to ignore conditionals for now, there are too many.
                    if egraph
                        .parse_and_run_program(
                            None,
                            format!("(check (cond-equal {term1} {term2}))").as_str(),
                        )
                        .is_ok()
                    {
                        info!("skipping");
                        continue;
                    }

                    // TODO: check if they are conditionally equal
                    let mut has_meaningful_diff = false;
                    let mut matching_count = 0;
                    let mut same_vals: Vec<bool> = vec![];

                    for (cvec_1_el, cvec_2_el) in cvec1.iter().zip(cvec2.iter()) {
                        let has_match = cvec_1_el == cvec_2_el;
                        if !has_match && cvec_1_el.is_some() || cvec_2_el.is_some() {
                            has_meaningful_diff = true;
                        }
                        same_vals.push(has_match);
                        if has_match {
                            matching_count += 1;
                        }
                    }

                    if !has_meaningful_diff {
                        continue;
                    }

                    // filter out bad predicates that only match on one value
                    if matching_count < 3 {
                        continue;
                    }

                    // sufficient and necessary conditions.
                    // we may want to experiment with just having sufficient conditions.
                    let masks = mask_to_preds.keys().filter(|mask| {
                        mask.iter()
                            .zip(same_vals.iter())
                            .all(|(mask_val, same_val)| mask_val == same_val)
                    });

                    for mask in masks {
                        // if the mask is completely false, skip it.
                        if mask.iter().all(|x| !x) {
                            continue;
                        }
                        let preds = mask_to_preds.get(mask).unwrap();
                        for pred in preds {
                            result.conditional.push(Rule {
                                condition: Some(Sexp::from_str(pred).unwrap()),
                                lhs: term1.clone(),
                                rhs: term2.clone(),
                            });
                            result.conditional.push(Rule {
                                condition: Some(Sexp::from_str(pred).unwrap()),
                                lhs: term2.clone(),
                                rhs: term1.clone(),
                            });
                        }
                    }
                }
            }
        }
        result
    }

    fn add_rewrite(&mut self, egraph: &mut EGraph, lhs: Sexp, rhs: Sexp) {
        let term1 = self.make_string_not_bad(lhs.to_string().as_str());
        let term2 = self.make_string_not_bad(rhs.to_string().as_str());
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

    fn add_conditional_rewrite(&mut self, egraph: &mut EGraph, cond: Sexp, lhs: Sexp, rhs: Sexp) {
        // TODO: @ninehusky: let's brainstorm ways to encode conditional equality with respect to a
        // specific condition (see #20).
        let _pred = self.make_string_not_bad(cond.to_string().as_str());

        let term1 = self.make_string_not_bad(lhs.to_string().as_str());
        let term2 = self.make_string_not_bad(rhs.to_string().as_str());
        info!(
            "adding conditional rewrite: {} -> {} if {}",
            term1, term2, _pred
        );
        info!("term2 has cvec: {:?}", self.interpret_term(&rhs));
        egraph
            .parse_and_run_program(
                None,
                format!(
                    r#"
                    (cond-equal {term1} {term2})
                    (cond-equal {term2} {term1})
            "#
                )
                .as_str(),
            )
            .unwrap();
    }

    // returns the productions in the language.
    // returns some array result, where result[i] contains
    // the productions that add `i` to the size of the program.
    fn productions(&self) -> Workload;
    fn atoms(&self) -> Workload;
    fn make_preds(&self) -> Workload;
    fn get_env(&self) -> &HashMap<String, Vec<Value<Self>>>;
    fn validate_rule(&self, rule: Rule) -> ValidationResult;
    fn interpret_term(&mut self, term: &ruler::enumo::Sexp) -> CVec<Self>;
    fn interpret_pred(&mut self, term: &ruler::enumo::Sexp) -> Vec<bool>;
}
