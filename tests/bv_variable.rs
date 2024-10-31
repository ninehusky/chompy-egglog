use chompy::{Chomper, Rule, Value};
use itertools::Itertools;
use log::warn;
use rand::{rngs::StdRng, Rng, SeedableRng};
use ruler::{
    enumo::{Pattern, Sexp, Workload},
    HashMap, HashSet, ValidationResult,
};
use std::str::FromStr;
use z3::ast::Ast;

use serde::{Deserialize, Serialize};

use chompy::utils::TERM_PLACEHOLDER;

#[derive(Hash, PartialEq, Eq, Clone, Debug)]
pub struct Bitvector {
    pub width: u64,
    pub value: u64,
}

const MAX_BITWIDTH: usize = 4;
const CVEC_LEN: usize = 6;

pub struct BitvectorChomper {
    pub value_env: HashMap<String, Vec<u64>>,
    pub term_memo: HashMap<String, Vec<Option<Bitvector>>>,
    pub pred_memo: HashMap<String, Vec<bool>>,
    pub rng: StdRng,
}

impl Chomper for BitvectorChomper {
    type Constant = Bitvector;
    type Value = u64;

    fn constant_pattern(&self) -> Pattern {
        "(Bitvector ?width (ValueNum ?value))".parse().unwrap()
    }

    fn matches_var_pattern(&self, term: &Sexp) -> bool {
        if let Sexp::List(l) = term {
            if l.len() == 2 {
                if let Sexp::Atom(a) = &l[0] {
                    return a == "ValueVar";
                }
            }
        }
        false
    }

    fn atoms(&self) -> Workload {
        // keeping this completely symbolic for now; we can add some form of constants later.
        Workload::new(&["(Bitvector (ValueVar WIDTH) (ValueVar VALUE))"])
            .plug("WIDTH", &Workload::new(&["p", "q"]))
            .plug("VALUE", &Workload::new(&["a", "b"]))
    }

    fn productions(&self) -> Workload {
        let unary_ops: Vec<&str> = vec![];
        let binary_ops = vec!["(Add)", "(Sub)", "(Mul)", "(Shl)", "(Shr)"];
        Workload::new(&[
            format!(
                "(BVOp2 width binop {} {})",
                TERM_PLACEHOLDER, TERM_PLACEHOLDER
            ),
            format!("(BVOp1 width unaryop {})", TERM_PLACEHOLDER),
        ])
        .plug("width", &Workload::new(&["(ValueVar p)", "(ValueVar q)"]))
        .plug("binop", &Workload::new(&binary_ops))
        .plug("unaryop", &Workload::new(&unary_ops))
    }

    fn interpret_term(&mut self, term: &ruler::enumo::Sexp) -> chompy::CVec<Self> {
        interpret_term_internal(term.clone(), &self.value_env, &mut self.term_memo)
    }

    fn interpret_pred(&mut self, pred: &ruler::enumo::Sexp) -> Vec<bool> {
        interpret_pred_internal(pred.clone(), &self.value_env, &mut self.pred_memo)
    }

    fn get_env(&self) -> &HashMap<String, Vec<Value<Self>>> {
        &self.value_env
    }

    fn get_validated_rule(&self, rule: &chompy::Rule) -> Option<Rule> {
        let widths: HashSet<String> = self
            .get_widths(&rule.lhs)
            .union(&self.get_widths(&rule.rhs))
            .cloned()
            .collect();

        let create_envs = || -> Vec<HashMap<String, usize>> {
            // create a list of k-tuples, where k = |widths|. Each element of the tuple
            // is a 2-tuple of (width, value). the list should be the cartesian product of
            // every width mapped to every value from 1..MAX_BITWIDTH.
            //
            let mut storage = vec![];

            for width in &widths {
                storage.push(
                    vec![width]
                        .into_iter()
                        .cartesian_product(1..MAX_BITWIDTH)
                        .collect::<Vec<_>>(),
                );
            }

            for val in &storage {
                // add everything else in storage to some vector. that is, create a vector containing
                // all elements of storage != val.
                let mut other_vals = vec![];
                for other in &storage {
                    if other != val {
                        other_vals.push(other);
                    }
                }
            }

            // now, get the cartesian product of all elements of storage.
            storage
                .into_iter()
                .multi_cartesian_product()
                .map(|tuple| {
                    let mut env = HashMap::default();
                    for (width, value) in tuple {
                        env.insert(width.clone(), value);
                    }
                    env
                })
                .collect::<Vec<_>>()
        };

        let envs = create_envs();
        let mut validation_results: Vec<ValidationResult> = vec![];

        for env in &envs[..] {
            let concrete = Self::concretize_rule(rule, &env);
            let lhs = &concrete.lhs;
            let rhs = &concrete.rhs;
            let mut cfg = z3::Config::new();
            cfg.set_timeout_msec(1000);
            let ctx = z3::Context::new(&cfg);
            let solver = z3::Solver::new(&ctx);
            let lexpr = sexpr_to_z3(self, &ctx, lhs);
            let rexpr = sexpr_to_z3(self, &ctx, rhs);
            solver.assert(&lexpr._eq(&rexpr).not());
            validation_results.push(match solver.check() {
                z3::SatResult::Unsat => ValidationResult::Valid,
                z3::SatResult::Unknown => ValidationResult::Unknown,
                z3::SatResult::Sat => ValidationResult::Invalid,
            });
        }

        #[derive(Serialize, Deserialize)]
        struct Results {
            bitwidths: HashSet<String>,
            good_envs: Vec<HashMap<String, usize>>,
            bad_envs: Vec<HashMap<String, usize>>,
            // TODO: @ninehusky - do we need this?
            // unknown_envs: Vec<HashMap<String, usize>>,
        }

        let mut good_envs: Vec<HashMap<String, usize>> = vec![];
        let mut bad_envs: Vec<HashMap<String, usize>> = vec![];

        assert_eq!(validation_results.len(), envs.len());
        for (result, env) in validation_results.iter().zip(envs.iter()) {
            match result {
                ValidationResult::Valid => good_envs.push(env.clone()),
                ValidationResult::Invalid => bad_envs.push(env.clone()),
                ValidationResult::Unknown => {
                    warn!("unknown validation result for env: {:?}", env);
                }
            }
        }

        if good_envs.is_empty() {
            return Some(Rule {
                condition: None,
                lhs: rule.lhs.clone(),
                rhs: rule.rhs.clone(),
            });
        }

        if bad_envs.is_empty() {
            return None;
        }

        let results = Results {
            bitwidths: widths.clone(),
            good_envs,
            bad_envs,
        };

        let json_str = serde_json::to_string(&results).unwrap();

        // save that to "my_file.json"
        // TODO: @ninehusky - use a temp file here rather than re-using the same one each time.
        std::fs::write("my_file.json", json_str).expect("Unable to write file");

        // now, start the racket process.
        let proc = std::process::Command::new("racket")
            .arg("./racket/infer-cond.rkt")
            .arg("--env-filepath")
            .arg("my_file.json")
            .output()
            .expect("failed to execute process");

        if !proc.status.success() {
            println!("error: {:?}", proc);
            return None;
        }

        let output_string = String::from_utf8_lossy(&proc.stdout).to_string();
        // this is CRAZY
        // get the substring from the third '(' character all the way to the second-to-last
        // character.
        // find the index of the third '('.
        let third_paren_index = output_string
            .as_str()
            .char_indices()
            .filter(|(_, c)| *c == '(')
            .nth(2)
            .unwrap()
            .0;

        let mut result_str = output_string[third_paren_index..output_string.len() - 1].to_string();
        // println!("condition: {}", result_str);
        for (i, bitwidth) in widths.clone().iter().enumerate() {
            let letter: char = (b'p' + i as u8) as char;
            // println!("replacing {} with {}", letter, bitwidth);
            let replaced = result_str.replace(&format!("{}", letter), &format!("{}", bitwidth));
            result_str = replaced.clone();
        }
        // println!("new condition: {}", result_str);

        let condition = Sexp::from_str(&result_str).unwrap();

        Some(Rule {
            condition: Some(condition),
            lhs: rule.lhs.clone(),
            rhs: rule.rhs.clone(),
        })
    }

    fn make_preds(&self) -> Workload {
        // TODO: expand this to include more meaningful predicates
        Workload::empty()
    }
}

impl BitvectorChomper {
    pub fn matches_const_pattern(&self, term: &Sexp) -> bool {
        if let Sexp::List(l) = term {
            if l.len() == 3 {
                if let Sexp::Atom(a) = &l[0] {
                    if a == "Bitvector" {
                        if let Sexp::List(l) = &l[2] {
                            if let Sexp::Atom(a) = &l[0] {
                                return a == "ValueNum";
                            }
                        }
                    }
                }
            }
        }
        false
    }
    fn concretize_rule(rule: &chompy::Rule, env: &HashMap<String, usize>) -> Rule {
        Rule {
            condition: None,
            lhs: Self::concretize_term(&rule.lhs, env),
            rhs: Self::concretize_term(&rule.rhs, env),
        }
    }

    fn concretize_term(term: &Sexp, env: &HashMap<String, usize>) -> Sexp {
        let mut term_str = term.to_string();
        for (var, value) in env {
            term_str = term_str.replace(var, format!("(ValueNum {})", value).as_str());
        }
        Sexp::from_str(&term_str).unwrap()
    }

    // NOTE: assumes that the term is generalized (that is, variables are just ?id rather than
    // `(ValueVar ?id)`).
    fn get_width(&self, term: &Sexp) -> String {
        match term {
            Sexp::Atom(_) => panic!("unexpected atom"),
            Sexp::List(l) => {
                // it will always be the second element.
                assert!(l.len() >= 2);
                if let Sexp::Atom(width) = &l[1] {
                    return width.clone();
                }
            }
        }
        panic!()
    }

    fn get_widths(&self, term: &Sexp) -> HashSet<String> {
        let mut result: HashSet<String> = HashSet::default();
        fn collect_widths(chomper: &BitvectorChomper, term: &Sexp, result: &mut HashSet<String>) {
            match term {
                Sexp::List(ref l) => {
                    result.insert(chomper.get_width(&term));
                    for term in l[3..].iter() {
                        collect_widths(chomper, term, result);
                    }
                }
                Sexp::Atom(_) => (),
            }
        }
        collect_widths(self, &term, &mut result);
        result
    }
}

fn sexpr_to_z3<'a>(
    chomper: &BitvectorChomper,
    ctx: &'a z3::Context,
    expr: &Sexp,
) -> z3::ast::BV<'a> {
    fn get_concrete_width(expr: &Sexp) -> u32 {
        if let Sexp::List(l) = expr {
            if let Sexp::List(l) = &l[1] {
                assert_eq!(2, l.len());
                match (l[0].to_string().as_str(), l[1].to_string().as_str()) {
                    ("ValueNum", width) => {
                        return width.parse::<u32>().unwrap();
                    }
                    ("ValueVar", _) => panic!("unexpected ValueVar in width"),
                    _ => panic!("unexpected width type"),
                };
            }
        }
        panic!("unexpected expression {:?}", expr);
    }
    if chomper.matches_const_pattern(expr) {
        let width = get_concrete_width(expr);
        let value = if let Sexp::List(l) = expr {
            if let Sexp::List(l) = &l[2] {
                if let Sexp::Atom(a) = &l[1] {
                    a.to_string().parse::<u64>().unwrap()
                } else {
                    panic!()
                }
            } else {
                panic!()
            }
        } else {
            panic!()
        };
        let bv_value = z3::ast::BV::from_u64(ctx, value, MAX_BITWIDTH.try_into().unwrap());
        z3::ast::BV::zero_ext(
            &z3::ast::BV::extract(&bv_value, width, 0),
            ((MAX_BITWIDTH as u32) - width).try_into().unwrap(),
        )
    } else {
        match expr {
            Sexp::List(l) => {
                let op = &l[0];
                if let Sexp::Atom(op_type) = op {
                    let width: u32 = get_concrete_width(expr);
                    let value = match op_type.as_str() {
                        "Bitvector" => {
                            assert_eq!(l.len(), 3);
                            let value = &l[2];
                            if let Sexp::Atom(a) = value {
                                assert!(a.starts_with("?"));
                                let stripped = a.strip_prefix("?").unwrap();
                                z3::ast::BV::new_const(
                                    ctx,
                                    stripped,
                                    MAX_BITWIDTH.try_into().unwrap(),
                                )
                            } else {
                                panic!()
                            }
                        }
                        "BVOp1" => {
                            assert_eq!(l.len(), 4);
                            let op = &l[2];
                            let children = &l[3..]
                                .into_iter()
                                .map(|arg| sexpr_to_z3(chomper, ctx, arg))
                                .collect::<Vec<_>>();
                            if let Sexp::List(op) = op {
                                assert_eq!(op.len(), 1);
                                match &op[0] {
                                    Sexp::Atom(op) => match op.as_str() {
                                        "Neg" => z3::ast::BV::bvneg(&children[0].clone()),
                                        "Not" => z3::ast::BV::bvnot(&children[0].clone()),
                                        _ => panic!("unknown operator {:?}", op),
                                    },
                                    _ => panic!("unexpected non-atom operator {:?}", op),
                                }
                            } else {
                                panic!();
                            }
                        }
                        "BVOp2" => {
                            assert_eq!(l.len(), 5);
                            let op = &l[2];
                            let children = &l[3..]
                                .into_iter()
                                .map(|arg| sexpr_to_z3(chomper, ctx, arg))
                                .collect::<Vec<_>>();
                            if let Sexp::List(op) = op {
                                assert_eq!(op.len(), 1);
                                match &op[0] {
                                    Sexp::Atom(op) => match op.as_str() {
                                        "Add" => z3::ast::BV::bvadd(&children[0], &children[1]),
                                        "Sub" => z3::ast::BV::bvsub(&children[0], &children[1]),
                                        "Mul" => z3::ast::BV::bvmul(&children[0], &children[1]),
                                        "Shl" => z3::ast::BV::bvshl(&children[0], &children[1]),
                                        "Shr" => z3::ast::BV::bvlshr(&children[0], &children[1]),
                                        // TODO: add these in later -- right now, they mess up type
                                        // checking.
                                        // "Lt" => z3::ast::BV::bvult(&children[0], &children[1]),
                                        // "Gt" => z3::ast::BV::bvugt(&children[0], &children[1]),
                                        _ => panic!("unknown operator {:?}", op),
                                    },
                                    _ => panic!("unexpected non-atom operator {:?}", op),
                                }
                            } else {
                                panic!();
                            }
                        }
                        _ => panic!("unknown operator {:?} in term {}", op, expr),
                    };
                    z3::ast::BV::zero_ext(
                        &z3::ast::BV::extract(&value, width, 0),
                        ((MAX_BITWIDTH as u32) - width).try_into().unwrap(),
                    )
                } else {
                    panic!();
                }
            }
            _ => panic!(),
        }
    }
}

impl Bitvector {
    fn new(width: u64, value: u64) -> Self {
        if width > MAX_BITWIDTH as u64 {
            panic!(
                "error: constructing bitvector with width {} that is greater than {}",
                width, MAX_BITWIDTH
            );
        }
        if value > (1 << width) {
            warn!(
                "warning: constructing bitvector with value {} that is greater than 2^{}",
                value, width
            );
        }
        Bitvector {
            width,
            value: value % (1 << width),
        }
    }
}

fn initialize_value_env(
    rng: &mut StdRng,
    vars: Vec<String>,
    min: u64,
    max: u64,
) -> HashMap<String, Vec<u64>> {
    let mut env: HashMap<String, Vec<u64>> = HashMap::default();
    for var in vars {
        if max - min < CVEC_LEN as u64 {
            let mut vals: Vec<u64> = vec![];
            while vals.len() < CVEC_LEN {
                let value: u64 = rng.gen_range(min..max);
                vals.push(value);
            }
            env.insert(var, vals);
        } else {
            let mut unique_vals: HashSet<u64> = HashSet::default();
            while unique_vals.len() < CVEC_LEN {
                let value: u64 = rng.gen_range(min..max);
                unique_vals.insert(value);
            }
            env.insert(var, unique_vals.into_iter().collect());
        }
    }
    env
}

fn interpret_pred_internal(
    pred: Sexp,
    value_env: &HashMap<String, Vec<u64>>,
    pred_memo: &mut HashMap<String, Vec<bool>>,
) -> Vec<bool> {
    if let Some(result) = pred_memo.get(&pred.to_string()) {
        return result.clone();
    }
    match pred {
        Sexp::List(l) => match l[0].to_string().as_str() {
            "PredOp2" => {
                assert!(l.len() == 4);
                let first_vvec = get_value_vec(l[2].clone(), value_env);
                let second_vvec = get_value_vec(l[3].clone(), value_env);
                let op = match &l[1] {
                    Sexp::List(l) => match &l[0] {
                        Sexp::Atom(op) => match op.as_str() {
                            "Eq" => |(a, b)| a == b,
                            "Neq" => |(a, b)| a != b,
                            "Le" => |(a, b)| a <= b,
                            "Ge" => |(a, b)| a >= b,
                            "Lt" => |(a, b)| a < b,
                            "Gt" => |(a, b)| a > b,
                            _ => panic!("unknown pred operator {:?}", l[1].to_string()),
                        },
                        _ => panic!(),
                    },
                    _ => panic!("pred operator should be an atom, but found {:?}", l[1]),
                };
                first_vvec.iter().zip(second_vvec.iter()).map(op).collect()
            }
            _ => panic!(),
        },
        _ => panic!(),
    }
}

fn get_value_vec(value: Sexp, value_env: &HashMap<String, Vec<u64>>) -> Vec<u64> {
    match value {
        Sexp::List(l) => match l[0].to_string().as_str() {
            "ValueVar" => {
                assert!(l.len() == 2);
                let value = value_env.get(&l[1].to_string()).unwrap();
                return value.clone();
            }
            "ValueNum" => {
                assert!(l.len() == 2);
                let value = l[1].to_string().parse::<u64>();
                vec![value.unwrap(); CVEC_LEN]
            }
            _ => panic!("unknown value operator {:?}", l[0].to_string()),
        },
        _ => panic!("value should be a list, but found {:?}", value),
    }
}

fn interpret_term_internal(
    term: ruler::enumo::Sexp,
    value_env: &HashMap<String, Vec<u64>>,
    memo: &mut HashMap<String, Vec<Option<Bitvector>>>,
) -> Vec<Option<Bitvector>> {
    if let Some(result) = memo.get(&term.to_string()) {
        return result.clone();
    }
    let cvec: Vec<Option<Bitvector>> = match term {
        Sexp::Atom(atom) => {
            panic!("You should not be interpreting mii: {:?}", atom);
        }
        Sexp::List(ref l) => {
            let op = l[0].to_string();
            match op.as_str() {
                "Bitvector" => {
                    let widths = get_value_vec(l[1].clone(), value_env);
                    let values = get_value_vec(l[2].clone(), value_env);
                    widths
                        .iter()
                        .zip(values.iter())
                        .map(|(width, value)| Some(Bitvector::new(*width, *value)))
                        .collect()
                }
                "BVOp1" => {
                    assert!(l.len() == 4);
                    let widths = get_value_vec(l[1].clone(), value_env);
                    let op = l[2].clone();
                    fn f(a: u64, op: &Sexp) -> Option<u64> {
                        match op {
                            Sexp::List(l) => {
                                assert!(l.len() == 1);
                                match l[0] {
                                    Sexp::Atom(ref op) => match op.as_str() {
                                        "Neg" => Some(a.overflowing_neg().0),
                                        "Not" => Some(if a == 0 { 1 } else { 0 }),
                                        _ => todo!("not implemented {:?}", op),
                                    },
                                    _ => panic!("expected atom, found {:?}", op),
                                }
                            }
                            _ => panic!("expected list, found {:?}", op),
                        }
                    }
                    let child_cvecs: Vec<Vec<Option<Bitvector>>> = l[3..4]
                        .iter()
                        .map(|x| interpret_term_internal(x.clone(), value_env, memo))
                        .into_iter()
                        .collect();

                    child_cvecs[0]
                        .iter()
                        .zip(widths.iter())
                        .map(|(first_child_val, width)| match first_child_val {
                            Some(first_child) => {
                                let result = f(first_child.value, &op);
                                match result {
                                    Some(result) => Some(Bitvector::new(*width, result)),
                                    None => None,
                                }
                            }
                            _ => None,
                        })
                        .collect()
                }
                "BVOp2" => {
                    assert!(l.len() == 5);
                    let widths = get_value_vec(l[1].clone(), value_env);
                    let op = l[2].clone();
                    // TODO: @ninehusky - macroify this f thing
                    fn f(a: u64, b: u64, op: &Sexp) -> Option<u64> {
                        match op {
                            Sexp::Atom(op) => panic!("expected list, found atom {:?}", op),
                            Sexp::List(l) => {
                                assert!(l.len() == 1);
                                match l[0] {
                                    Sexp::Atom(ref op) => match op.as_str() {
                                        "Add" => Some(a.overflowing_add(b).0),
                                        "Sub" => Some(a.overflowing_sub(b).0),
                                        "Mul" => Some(a.overflowing_mul(b).0),
                                        "Shl" => Some(a.overflowing_shl(b as u32).0),
                                        "Shr" => Some(a.overflowing_shr(b as u32).0),
                                        "Lt" => Some(if a < b { 1 } else { 0 }),
                                        "Gt" => Some(if a > b { 1 } else { 0 }),
                                        _ => todo!("not implemented {:?}", op),
                                    },
                                    _ => panic!("expected atom, found {:?}", op),
                                }
                            }
                        }
                    }
                    let child_cvecs: Vec<Vec<Option<Bitvector>>> = l[3..5]
                        .iter()
                        .map(|x| interpret_term_internal(x.clone(), value_env, memo))
                        .into_iter()
                        .collect();

                    child_cvecs[0]
                        .iter()
                        .zip(child_cvecs[1].iter())
                        .zip(widths.iter())
                        .map(|((first_child_val, second_child_val), width)| {
                            match (first_child_val, second_child_val) {
                                (Some(first_child), Some(second_child)) => {
                                    let result = f(first_child.value, second_child.value, &op);
                                    match result {
                                        Some(result) => Some(Bitvector::new(*width, result)),
                                        None => None,
                                    }
                                }
                                _ => None,
                            }
                        })
                        .collect()
                }
                _ => panic!(
                    "found weird operator {:?} in term {:?}",
                    op.as_str(),
                    term.to_string()
                ),
            }
        }
    };
    memo.insert(term.to_string(), cvec.clone());
    cvec
}

mod tests {
    use chompy::init_egraph;

    use super::*;

    #[test]
    pub fn bv_variable() {
        let mut rng = StdRng::seed_from_u64(0xdeadbeef);
        let width_env = initialize_value_env(
            &mut rng,
            vec!["p".to_string(), "q".to_string()],
            0,
            (MAX_BITWIDTH + 1).try_into().unwrap(),
        );
        println!("{:?}", width_env);
        let value_env = initialize_value_env(
            &mut rng,
            vec!["a".to_string(), "b".to_string()],
            0,
            (1 << MAX_BITWIDTH) - 1,
        );
        println!("{:?}", value_env);

        // final env should be the combination of these two.
        let final_env = width_env
            .iter()
            .chain(value_env.iter())
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect::<HashMap<_, _>>();

        let mut chomper = BitvectorChomper {
            value_env: final_env,
            term_memo: HashMap::default(),
            pred_memo: HashMap::default(),
            rng,
        };

        let mut egraph = egglog::EGraph::default();
        init_egraph!(egraph, "./egglog/bv-variable.egg");
        chomper.run_chompy(
            &mut egraph,
            vec![],
            &HashMap::default(),
            &mut HashSet::default(),
        );
    }
}
