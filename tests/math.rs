use chompy::{utils::TERM_PLACEHOLDER, CVec, Chomper, Rule, Value};
use enumo::{Pattern, Sexp, Workload};
use ruler::*;
use std::str::FromStr;

const CVEC_LEN: usize = 10;

struct MathLanguage {
    env: HashMap<String, Vec<Value<Self>>>,
}

impl MathLanguage {
    fn default() -> Self {
        // a dummy environment, since we don't use it.
        let mut env: HashMap<String, Vec<Value<Self>>> = HashMap::default();
        env.insert("a".to_string(), vec![1; CVEC_LEN]);
        Self { env }
    }
}

impl Chomper for MathLanguage {
    type Constant = i64;
    // we'll never use this, but it has to be here.
    type Value = i64;

    fn get_constant_pattern(&self) -> Pattern {
        "(Num ?n)".parse().unwrap()
    }

    // In this language, all variables take on the same value.
    // See `interpret_term` for how we handle variables.
    fn get_env(&self) -> &HashMap<String, Vec<Value<Self>>> {
        &self.env
    }

    fn atoms(&self) -> Workload {
        Workload::new(&["(Num 0)", "(Num 1)", "(Var a)"])
    }

    fn productions(&self) -> Workload {
        Workload::new(&[
            format!(
                "(MathOp2 binaryop {} {})",
                TERM_PLACEHOLDER, TERM_PLACEHOLDER
            ),
            format!("(MathOp1 unaryop {})", TERM_PLACEHOLDER),
        ])
        .plug(
            "binaryop",
            &Workload::new(&["(Add)", "(Sub)", "(Mul)", "(Div)"]),
        )
        .plug("unaryop", &Workload::new(&["(Abs)"]))
    }

    fn make_preds(&self) -> Workload {
        Workload::new(&["(PredOp2 predop x y)"])
            .plug(
                "predop",
                &Workload::new(&["(Eq)", "(Neq)", "(Gt)", "(Ge)", "(Ge)", "(Lt)"]),
            )
            .plug(
                "x",
                &Workload::new(&[
                    "(Num 0)",
                    "(Num 1)",
                    "(Var a)",
                    "(MathOp2 (Div) (Var a) (Var a))",
                ]),
            )
            .plug(
                "y",
                &Workload::new(&[
                    "(Num 0)",
                    "(Num 1)",
                    "(Var a)",
                    "(MathOp2 (Div) (Var a) (Var a))",
                ]),
            )
    }

    fn validate_rule(&self, _rule: Rule) -> ValidationResult {
        ValidationResult::Valid
    }

    fn interpret_pred(&mut self, term: &Sexp) -> Vec<bool> {
        let sexp = term;
        let mut cvec = vec![];
        match sexp {
            Sexp::Atom(_) => {
                panic!("uhh");
            }
            Sexp::List(ref l) => {
                let op = l[0].to_string();
                match op.as_str() {
                    "PredOp2" => {
                        assert!(l.len() == 4);
                        let op = l[1].to_string();
                        let x = self.interpret_term(&l[2]);
                        let y = self.interpret_term(&l[3]);
                        let my_fn = match op.as_str() {
                            "(Eq )" => i64::eq,
                            "(Neq )" => i64::ne,
                            "(Gt )" => i64::gt,
                            "(Ge )" => i64::ge,
                            "(Lt )" => i64::lt,
                            _ => unreachable!(),
                        };
                        for (x_el, y_el) in x.iter().zip(y.iter()) {
                            if x_el.is_none() || y_el.is_none() {
                                // TODO: this should push None
                                cvec.push(false);
                            } else {
                                cvec.push(my_fn(&x_el.unwrap(), &y_el.unwrap()));
                            }
                        }
                        cvec
                    }
                    _ => unreachable!(),
                }
            }
        }
    }

    fn interpret_term(&mut self, term: &Sexp) -> CVec<Self> {
        let cvec_sexp = term;
        match cvec_sexp {
            Sexp::Atom(_) => {
                panic!("uhh");
            }
            Sexp::List(ref l) => {
                let op = l[0].to_string();
                match op.as_str() {
                    "Num" => {
                        assert!(l.len() == 2);
                        let num = l[1].to_string().parse::<i64>().unwrap();
                        return vec![Some(num); CVEC_LEN];
                    }
                    "Var" => {
                        assert!(l.len() == 2);
                        // get range centered at 0 of length CVEC_LEN
                        let cvec_len_as_i64 = CVEC_LEN as i64;
                        return (-cvec_len_as_i64 / 2..cvec_len_as_i64 / 2)
                            .map(|x| Some(x))
                            .collect::<Vec<_>>();
                    }
                    "MathOp1" => {
                        assert!(l.len() == 3);
                        let op = l[1].to_string();
                        let x = self.interpret_term(&l[2]);
                        let mut result = vec![];
                        for x_el in x.iter() {
                            result.push({
                                if x_el.is_none() {
                                    None
                                } else {
                                    match op.as_str() {
                                        "(Abs )" => x_el.unwrap().checked_abs(),
                                        _ => unreachable!("uhh"),
                                    }
                                }
                            });
                        }
                        return result;
                    }
                    "MathOp2" => {
                        assert!(l.len() == 4);
                        let op = l[1].to_string();
                        let x = self.interpret_term(&l[2]);
                        let y = self.interpret_term(&l[3]);
                        let mut result = vec![];
                        for (x_el, y_el) in x.iter().zip(y.iter()) {
                            result.push({
                                if x_el.is_none() || y_el.is_none() {
                                    None
                                } else {
                                    match op.as_str() {
                                        "(Add )" => x_el.unwrap().checked_add(y_el.unwrap()),
                                        "(Sub )" => x_el.unwrap().checked_sub(y_el.unwrap()),
                                        "(Mul )" => x_el.unwrap().checked_mul(y_el.unwrap()),
                                        "(Div )" => x_el.unwrap().checked_div(y_el.unwrap()),
                                        _ => unreachable!("received op: {}", op),
                                    }
                                }
                            });
                        }
                        return result;
                    }
                    _ => unreachable!(),
                }
            }
        }
    }
}

#[test]
fn math_eval() {
    let mut egraph = egglog::EGraph::default();
    egraph
        .parse_and_run_program(
            Some("./egglog/math.egg".to_string()),
            include_str!("./egglog/math.egg"),
        )
        .unwrap();

    let mut chomper = MathLanguage::default();

    let mask_to_preds = chomper.make_mask_to_preds();

    chomper.run_chompy(
        &mut egraph,
        vec![
            Rule {
                condition: Some(
                    Sexp::from_str("(PredOp2 (Neq) (MathOp2 (Div) (Var a) (Var a)) (Num 0))")
                        .unwrap(),
                ),
                lhs: Sexp::from_str("(MathOp2 (Div) (Var a) (Var a))").unwrap(),
                rhs: Sexp::from_str("(Num 1)").unwrap(),
            },
            Rule {
                condition: Some(Sexp::from_str("(PredOp2 (Ge) (Var a) (Num 0))").unwrap()),
                lhs: Sexp::from_str("(MathOp1 (Abs) (Var a))").unwrap(),
                rhs: Sexp::from_str("(Var a)").unwrap(),
            },
        ],
        &mask_to_preds,
    );
}
