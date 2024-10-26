use chompy::{init_egraph, Chomper, Value};
use rand::{rngs::StdRng, Rng, SeedableRng};
use ruler::{
    enumo::{Pattern, Sexp, Workload},
    HashMap, HashSet, ValidationResult,
};

use chompy::Rule;
use log::warn;

use egglog::EGraph;

use std::str::FromStr;

use chompy::utils::TERM_PLACEHOLDER;

#[derive(Hash, PartialEq, Eq, Clone, Debug)]
pub struct Bitvector {
    pub width: u64,
    pub value: u64,
}

const MAX_BITWIDTH: usize = 4;
const CVEC_LEN: usize = 50;

pub struct BitvectorChomper {
    pub value_env: HashMap<String, Vec<u64>>,
    pub term_memo: HashMap<String, Vec<Option<Bitvector>>>,
    pub pred_memo: HashMap<String, Vec<bool>>,
    pub rng: StdRng,
}

impl Chomper for BitvectorChomper {
    type Constant = Bitvector;
    type Value = u64;

    fn matches_var_pattern(&self, term: &Sexp) -> bool {
        if let Sexp::List(l) = term {
            if l.len() == 3 {
                if let Sexp::Atom(a) = &l[0] {
                    if a == "Bitvector" {
                        if let Sexp::List(l) = &l[2] {
                            if let Sexp::Atom(a) = &l[0] {
                                return a == "ValueVar";
                            }
                        }
                    }
                }
            }
        }
        false
    }

    fn constant_pattern(&self) -> Pattern {
        "(Bitvector ?width (ValueNum ?value))".parse().unwrap()
    }

    fn atoms(&self) -> Workload {
        Workload::new(&[
            "(Bitvector (ValueNum 4) (ValueNum 1))",
            "(Bitvector (ValueNum 4) (ValueNum 2))",
            // "(Bitvector (ValueNum 4) (ValueNum 3))",
            "(Bitvector (ValueNum 4) (ValueVar p))",
            "(Bitvector (ValueNum 4) (ValueVar q))",
            "(Bitvector (ValueNum 4) (ValueVar r))",
        ])
    }

    fn productions(&self) -> Workload {
        let unary_ops = vec!["(Neg)", "(Not)"];
        let binary_ops = vec!["(Add)", "(Sub)", "(Mul)", "(Shl)", "(Shr)", "(Lt)", "(Gt)"];
        Workload::new(&[
            format!("(BVOp2 binop {} {})", TERM_PLACEHOLDER, TERM_PLACEHOLDER),
            format!("(BVOp1 unaryop {})", TERM_PLACEHOLDER),
        ])
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

    // hehe
    fn validate_rule(&self, _rule: &chompy::Rule) -> ValidationResult {
        ValidationResult::Valid
    }

    fn make_preds(&self) -> Workload {
        // TODO: expand this to include more meaningful predicates
        Workload::new(&[r#"(PredOp2 (Le) (ValueVar "r") (ValueVar "p"))"#])
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
            // make vector from min to max, repeat it and take CVEC_LEN elements.
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
                    assert!(l.len() == 3);
                    let op = l[1].clone();
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
                    let child_cvecs: Vec<Vec<Option<Bitvector>>> = l[2..3]
                        .iter()
                        .map(|x| interpret_term_internal(x.clone(), value_env, memo))
                        .into_iter()
                        .collect();

                    child_cvecs[0]
                        .iter()
                        .map(|val| match val {
                            Some(first_child) => {
                                let result = f(first_child.value, &op);
                                match result {
                                    Some(result) => Some(Bitvector::new(4, result)),
                                    None => None,
                                }
                            }
                            _ => None,
                        })
                        .collect()
                }
                "BVOp2" => {
                    assert!(l.len() == 4);
                    let op = l[1].clone();
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
                    let child_cvecs: Vec<Vec<Option<Bitvector>>> = l[2..4]
                        .iter()
                        .map(|x| interpret_term_internal(x.clone(), value_env, memo))
                        .into_iter()
                        .collect();

                    child_cvecs[0]
                        .iter()
                        .zip(child_cvecs[1].iter())
                        .map(|(first_child_val, second_child_val)| {
                            match (first_child_val, second_child_val) {
                                (Some(first_child), Some(second_child)) => {
                                    let result = f(first_child.value, second_child.value, &op);
                                    match result {
                                        Some(result) => Some(Bitvector::new(4, result)),
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

pub mod bv_tests {
    use crate::*;

    #[test]
    // finds (x * 2) ~> (x << 1)
    pub fn test_bv4_finds_shift_optimizer() {
        let mut rng = StdRng::seed_from_u64(0xdeadbeef);
        let value_env = initialize_value_env(
            &mut rng,
            vec!["p".to_string(), "q".to_string(), "r".to_string()],
            0,
            (1 << MAX_BITWIDTH) - 1,
        );

        let mut chomper = BitvectorChomper {
            value_env,
            term_memo: HashMap::default(),
            pred_memo: HashMap::default(),
            rng: StdRng::seed_from_u64(0xdeadbeef),
        };

        let mut egraph = EGraph::default();
        init_egraph!(egraph, "./egglog/bv4.egg");

        let mask_to_preds = chomper.make_mask_to_preds();
        chomper.run_chompy(
            &mut egraph,
            vec![Rule {
                condition: None,
                lhs: Sexp::from_str("(BVOp2 (Shl) (Bitvector (ValueNum 4) (ValueVar p)) (Bitvector (ValueNum 4) (ValueNum 1)))").unwrap(),
                rhs: Sexp::from_str("(BVOp2 (Mul) (Bitvector (ValueNum 4) (ValueVar p)) (Bitvector (ValueNum 4) (ValueNum 2)))").unwrap(),
            }],
            &mask_to_preds,
        );
    }
}
