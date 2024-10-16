use rand::{rngs::StdRng, Rng, SeedableRng};
use ruler::{enumo::Sexp, HashMap, HashSet};

use std::str::FromStr;

#[derive(Hash, PartialEq, Eq, Clone, Debug)]
pub struct Bitvector {
    pub width: u64,
    pub value: u64,
}

const MAX_BITWIDTH: usize = 4;
const CVEC_LEN: usize = 10;

impl Bitvector {
    fn new(width: u64, value: u64) -> Self {
        if width > MAX_BITWIDTH as u64 {
            panic!(
                "error: constructing bitvector with width {} that is greater than {}",
                width, MAX_BITWIDTH
            );
        }
        if value > (1 << width) {
            println!(
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

fn initialize_env(vars: Vec<String>) -> HashMap<String, Vec<Option<Bitvector>>> {
    let mut env: HashMap<String, Vec<Option<Bitvector>>> = HashMap::default();
    let mut rng = StdRng::seed_from_u64(0xdeadbeef);
    for var in vars {
        let mut unique_bvs: HashSet<Option<Bitvector>> = HashSet::default();
        while unique_bvs.len() < CVEC_LEN {
            let width: u64 = rng.gen_range(1..=(MAX_BITWIDTH as u64));
            let value: u64 = rng.gen_range(0..(1 << width) - 1);
            unique_bvs.insert(Some(Bitvector { width, value }));
        }
        env.insert(var, unique_bvs.into_iter().collect());
    }
    env
}

fn initialize_value_env(vars: Vec<String>, min: u64, max: u64) -> HashMap<String, Vec<u64>> {
    let mut env: HashMap<String, Vec<u64>> = HashMap::default();
    let mut rng = StdRng::seed_from_u64(0xdeadbeef);
    for var in vars {
        if max - min < CVEC_LEN as u64 {
            // make vector from min to max, repeat it and take CVEC_LEN elements.
            env.insert(var, (min..max).cycle().take(CVEC_LEN).collect());
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

fn interpret_term(
    term: ruler::enumo::Sexp,
    var_env: &HashMap<String, Vec<Option<Bitvector>>>,
    value_env: &HashMap<String, Vec<u64>>,
    memo: &mut HashMap<String, Vec<Option<Bitvector>>>,
) -> Vec<Option<Bitvector>> {
    println!("interpreting : {:?}", term.clone());
    let get_value_vec = |value: Sexp| -> Vec<u64> {
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
    };

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
                    let widths = get_value_vec(l[1].clone());
                    let values = get_value_vec(l[2].clone());
                    widths
                        .iter()
                        .zip(values.iter())
                        .map(|(width, value)| Some(Bitvector::new(*width, *value)))
                        .collect()
                }
                "BVOp1" => {
                    assert!(l.len() == 4);
                    let op = l[1].to_string();
                    let arg = interpret_term(l[2].clone(), var_env, value_env, memo);
                    match op.as_str() {
                        "(Neg)" => arg
                            .iter()
                            .map(|bv| match bv {
                                Some(bv) => Some(Bitvector::new(bv.width, !bv.value + 1)),
                                None => None,
                            })
                            .collect(),
                        _ => panic!("found weird operator {:?} in term {:?}", op.as_str(), term),
                    }
                }
                "BVOp2" => {
                    assert!(l.len() == 5);
                    let widths = get_value_vec(l[1].clone());
                    let op = l[2].clone();
                    fn f(a: u64, b: u64, op: &Sexp) -> Option<u64> {
                        match op {
                            Sexp::Atom(op) => panic!("expected list, found atom {:?}", op),
                            Sexp::List(l) => {
                                assert!(l.len() == 1);
                                match l[0] {
                                    Sexp::Atom(ref op) => match op.as_str() {
                                        "Add" => Some(a + b),
                                        _ => todo!("not implemented {:?}", op),
                                    },
                                    _ => panic!("expected atom, found {:?}", op),
                                }
                            }
                        }
                    }
                    println!("l[2] is {:?}", l[2].clone());
                    let child_cvecs: Vec<Vec<Option<Bitvector>>> = l[3..5]
                        .iter()
                        .map(|x| interpret_term(x.clone(), var_env, value_env, memo))
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

#[test]
pub fn run_bv4_eval() {
    let mut egraph = egglog::EGraph::default();
    egraph
        .parse_and_run_program(
            Some("./egglog/bv4.egg".to_string()),
            include_str!("./egglog/bv4.egg"),
        )
        .unwrap();

    let extraction = egraph
        .parse_and_run_program(
            None,
            r#"
        ;;; keep the lowest bit
        (let expr0 (BVOp2 (ValueNum 2) (Add) (Bitvector (ValueNum 3) (ValueNum 3)) (Bitvector (ValueNum 3) (ValueNum 2))))
        (extract expr0)
        "#,
        )
        .unwrap();

    println!("extraction: {:?}", extraction);
    let value_env = initialize_value_env(vec!["x".to_string()], 0, (1 << MAX_BITWIDTH) - 1);
    let width_env = initialize_value_env(vec!["p".to_string()], 1, MAX_BITWIDTH as u64);
    // intersect the maps.
    let value_env: HashMap<String, Vec<u64>> = value_env
        .into_iter()
        .chain(width_env.into_iter())
        .collect::<HashMap<String, Vec<u64>>>();
    let var_env = initialize_env(vec!["a".to_string(), "b".to_string()]);
    let cvec = interpret_term(
        Sexp::from_str(extraction[0].as_str()).unwrap(),
        &var_env,
        &value_env,
        &mut HashMap::default(),
    );
    println!("cvec: {:#?}", cvec);
}
