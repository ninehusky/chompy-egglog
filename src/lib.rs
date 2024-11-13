use egglog::{EGraph, SerializeConfig};
use ruler::enumo::Pattern;
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

    fn run_chompy(&mut self, egraph: &mut EGraph) {
        let mut max_eclass_id = 0;

        for current_size in 0..MAX_SIZE {
            println!("adding programs of size {}:", current_size);

            // let mut filter = Filter::MetricEq(Metric::Atoms, current_size);
            // if current_size > 4 {
            //     filter = Filter::And(vec![filter, Filter::Excludes(self.constant_pattern())]);
            // }

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

            let new_workload = if term_workload.force().is_empty() {
                self.atoms().clone()
            } else {
                self.productions()
                    .clone()
                    .plug(TERM_PLACEHOLDER, &term_workload)
            };

            println!("new workload len: {}", new_workload.force().len());

            let atoms = self.atoms().force();

            let memo = &mut HashSet::default();

            for term in &new_workload.force() {
                // println!("term: {}", term);
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
                for val in &vals.conditional {
                    let generalized = self.generalize_rule(val);
                    if let ValidationResult::Valid = self.validate_rule(&generalized) {
                        if utils::does_rule_have_good_vars(&generalized) {
                            let lhs =
                                self.make_string_not_bad(generalized.lhs.to_string().as_str());
                            let rhs =
                                self.make_string_not_bad(generalized.rhs.to_string().as_str());
                            let cond = generalized.condition.as_ref().unwrap();
                            let pred = self.make_string_not_bad(cond.to_string().as_str());
                            println!("Conditional rule: if {} then {} ~> {}", pred, lhs, rhs);
                            self.add_conditional_rewrite(
                                egraph,
                                Sexp::from_str(&pred).unwrap(),
                                Sexp::from_str(&lhs).unwrap(),
                                Sexp::from_str(&rhs).unwrap(),
                            );
                        }
                    }
                }
                for val in &vals.non_conditional {
                    let generalized = self.generalize_rule(val);
                    if let ValidationResult::Valid = self.validate_rule(&generalized) {
                        if utils::does_rule_have_good_vars(&generalized) {
                            let lhs =
                                self.make_string_not_bad(generalized.lhs.to_string().as_str());
                            let rhs =
                                self.make_string_not_bad(generalized.rhs.to_string().as_str());

                            if egraph
                                .parse_and_run_program(
                                    None,
                                    format!(r#"(check (= {} {}))"#, val.lhs, val.rhs).as_str(),
                                )
                                .is_ok()
                            {
                                continue;
                            }

                            self.add_rewrite(
                                egraph,
                                Sexp::from_str(&lhs).unwrap(),
                                Sexp::from_str(&rhs).unwrap(),
                            );
                            // TODO: derivability check here
                        }
                    } else {
                        // println!(
                        //     "perfect cvec match but failed validation: {} ~> {}",
                        //     val.lhs, val.rhs
                        // );
                    }
                }
            }
        }

        panic!("not all rules were found");
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
        let condition = match &rule.condition {
            Some(cond) => Some(self.generalize_sexp(cond.clone(), &mut id_to_gen_id)),
            None => None,
        };
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
        let serialized = egraph.serialize(SerializeConfig::default());
        println!("eclasses in egraph: {}", serialized.classes().len());
        println!("nodes in egraph: {}", serialized.nodes.len());
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

    fn add_rewrite(&mut self, egraph: &mut EGraph, lhs: Sexp, rhs: Sexp) {
        let term1 = self.make_string_not_bad(lhs.to_string().as_str());
        let term2 = self.make_string_not_bad(rhs.to_string().as_str());
        if term1 == "?a" {
            return;
        }
        println!("Rule: {} ~> {}", term1, term2);
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

    fn add_conditional_rewrite(
        &mut self,
        _egraph: &mut EGraph,
        _cond: Sexp,
        _lhs: Sexp,
        _rhs: Sexp,
    ) {
        // TODO: @ninehusky: let's brainstorm ways to encode conditional equality with respect to a
        // specific condition (see #20).
        // let _pred = self.make_string_not_bad(cond.to_string().as_str());
        // let term1 = self.make_string_not_bad(lhs.to_string().as_str());
        // let term2 = self.make_string_not_bad(rhs.to_string().as_str());
        // println!(
        //     "adding conditional rewrite: {} -> {} if {}",
        //     term1, term2, _pred
        // );
        // println!("term2 has cvec: {:?}", self.interpret_term(&rhs));
        // egraph
        //     .parse_and_run_program(
        //         None,
        //         format!(
        //             r#"
        //             (cond-equal {term1} {term2})
        //             (cond-equal {term2} {term1})
        //     "#
        //         )
        //         .as_str(),
        //     )
        //     .unwrap();
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

    fn productions(&self) -> Workload;
    fn atoms(&self) -> Workload;
    fn make_preds(&self) -> Workload;
    fn get_env(&self) -> &HashMap<String, CVec<Self>>;
    fn validate_rule(&self, rule: &Rule) -> ValidationResult;
    fn interpret_term(&mut self, term: &ruler::enumo::Sexp) -> CVec<Self>;
    fn interpret_pred(&mut self, term: &ruler::enumo::Sexp) -> Vec<bool>;
    fn constant_pattern(&self) -> Pattern;
    fn matches_var_pattern(&self, term: &Sexp) -> bool;
}
