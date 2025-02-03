// Smoketest to see how we can use Egg to do Chompy.

use egg::*;
use ruler::{
    enumo::{Filter, Metric, Workload},
    recipe_utils::{base_lang, iter_metric, Lang},
    IndexMap,
};

use num::Zero;

#[macro_export]
macro_rules! map {
    ($get:ident, $a:ident => $body:expr) => {
        $get($a)
            .iter()
            .map(|a| match a {
                Some($a) => $body,
                _ => None,
            })
            .collect::<Vec<_>>()
    };

    ($get:ident, $a:ident, $b:ident => $body:expr) => {
        $get($a)
            .iter()
            .zip($get($b).iter())
            .map(|tup| match tup {
                (Some($a), Some($b)) => $body,
                _ => None,
            })
            .collect::<Vec<_>>()
    };
    ($get:ident, $a:ident, $b:ident, $c:ident => $body:expr) => {
        $get($a)
            .iter()
            .zip($get($b).iter())
            .zip($get($c).iter())
            .map(|tup| match tup {
                ((Some($a), Some($b)), Some($c)) => $body,
                _ => None,
            })
            .collect::<Vec<_>>()
    };
}

egg::define_language! {
  pub enum HalideLanguage {
    Lit(i64),
    "<" = Lt([Id;2]),
    "<=" = Leq([Id;2]),
    "==" = Eq([Id;2]),
    "!=" = Neq([Id;2]),
    "->" = Implies([Id; 2]),
    "!" = Not(Id),
    "-" = Neg(Id),
    "&&" = And([Id;2]),
    "||" = Or([Id;2]),
    "^" = Xor([Id;2]),
    "+" = Add([Id; 2]),
    "-" = Sub([Id; 2]),
    "*" = Mul([Id; 2]),
    "/" = Div([Id; 2]),
    "min" = Min([Id; 2]),
    "max" = Max([Id; 2]),
    "select" = Select([Id; 3]),
    Var(Symbol),
  }
}

impl HalideLanguage {
    fn eval<'a, F>(&'a self, cvec_len: usize, mut get_cvec: F) -> Vec<Option<i64>>
    where
        F: FnMut(&'a Id) -> &'a Vec<Option<i64>>,
    {
        let one: i64 = 1;
        let zero: i64 = 0;
        match self {
            HalideLanguage::Lit(c) => vec![Some(c.clone()); cvec_len],
            HalideLanguage::Lt([x, y]) => {
                map!(get_cvec, x, y => if x < y {Some(one.clone())} else {Some(zero.clone())})
            }
            HalideLanguage::Leq([x, y]) => {
                map!(get_cvec, x, y => if x <= y {Some(one.clone())} else {Some(zero.clone())})
            }
            HalideLanguage::Eq([x, y]) => {
                map!(get_cvec, x, y => if x == y {Some(one.clone())} else {Some(zero.clone())})
            }
            HalideLanguage::Neq([x, y]) => {
                map!(get_cvec, x, y => if x != y {Some(one.clone())} else {Some(zero.clone())})
            }
            HalideLanguage::Implies([x, y]) => {
                map!(get_cvec, x, y => {
                  let xbool = x.clone() != zero;
                  let ybool = y.clone() != zero;
                  if !xbool || ybool {Some(one.clone())} else {Some(zero.clone())}
                })
            }
            HalideLanguage::Not(x) => {
                map!(get_cvec, x => if x.clone() == zero { Some(one.clone())} else {Some(zero.clone())})
            }
            HalideLanguage::Neg(x) => map!(get_cvec, x => Some(-x)),
            HalideLanguage::And([x, y]) => {
                map!(get_cvec, x, y => {
                    let xbool = x.clone() != zero;
                    let ybool = y.clone() != zero;
                    if xbool && ybool { Some(one.clone()) } else { Some(zero.clone()) }
                })
            }
            HalideLanguage::Or([x, y]) => {
                map!(get_cvec, x, y => {
                    let xbool = x.clone() != zero;
                    let ybool = y.clone() != zero;
                    if xbool || ybool { Some(one.clone()) } else { Some(zero.clone()) }
                })
            }
            HalideLanguage::Xor([x, y]) => {
                map!(get_cvec, x, y => {
                    let xbool = x.clone() != zero;
                    let ybool = y.clone() != zero;
                    if xbool ^ ybool { Some(one.clone()) } else { Some(zero.clone()) }
                })
            }
            HalideLanguage::Add([x, y]) => map!(get_cvec, x, y => x.checked_add(*y)),
            HalideLanguage::Sub([x, y]) => map!(get_cvec, x, y => x.checked_sub(*y)),
            HalideLanguage::Mul([x, y]) => map!(get_cvec, x, y => x.checked_mul(*y)),
            HalideLanguage::Div([x, y]) => map!(get_cvec, x, y => {
              if y.is_zero() {
                Some(zero.clone())
              } else {
                x.checked_div(*y)
              }
            }),
            HalideLanguage::Min([x, y]) => map!(get_cvec, x, y => Some(x.min(y).clone())),
            HalideLanguage::Max([x, y]) => map!(get_cvec, x, y => Some(x.max(y).clone())),
            HalideLanguage::Select([x, y, z]) => map!(get_cvec, x, y, z => {
              let xbool = x.clone() != zero;
              if xbool {Some(y.clone())} else {Some(z.clone())}
            }),
            HalideLanguage::Var(_) => vec![],
        }
    }
}

#[derive(Default)]
pub struct HalideAnalysis {
    pub size: i64,
}

impl Analysis<HalideLanguage> for HalideAnalysis {
    type Data = Vec<Option<i64>>;
    fn make(egraph: &mut EGraph<HalideLanguage, Self>, enode: &HalideLanguage) -> Self::Data {
        enode.eval(10, |id| &egraph[*id].data)
    }

    fn merge(&mut self, a: &mut Self::Data, b: Self::Data) -> DidMerge {
        egg::merge_max(a, b)
    }
}

struct Rule {
    lhs: RecExpr<HalideLanguage>,
    rhs: RecExpr<HalideLanguage>,
}

fn cvec_match(egraph: &EGraph<HalideLanguage, HalideAnalysis>) -> Vec<Rule> {
    let mut idx = 0;
    for ec1 in egraph.classes() {
        idx += 1;
        // go over everything in ec1 ...
        for ec2 in egraph.classes().skip(idx) {
            if ec1.data == ec2.data {
                // here is where we cvec match
                let extractor = Extractor::new(egraph, AstSize);
                let (_, t1) = extractor.find_best(ec1.id);
                let (_, t2) = extractor.find_best(ec2.id);
                println!("data: {:?}", ec1.data);
                panic!("{} ~> {}", t1, t2);
            }
        }
    }
    vec![]
}

fn main() {
    let max_size = 5;
    let mut egraph = EGraph::<HalideLanguage, HalideAnalysis>::default();

    let lang = Lang::new(
        &["-1", "0", "1"],
        &["a", "b", "c"],
        &[
            &["-", "!"],
            &[
                "&&", "||", "^", "+", "-", "*", "min", "max", "<", "<=", "==", "!=",
            ],
            &["select"],
        ],
    );

    let base_lang = if lang.ops.len() == 2 {
        base_lang(2)
    } else {
        base_lang(3)
    };
    for size in 1..max_size {
        println!("size: {}", size);
        let wkld = iter_metric(base_lang.clone(), "EXPR", Metric::Atoms, size)
            .filter(Filter::Contains("VAR".parse().unwrap()))
            .plug("OP1", &Workload::new(lang.ops[0].clone()))
            .plug("OP2", &Workload::new(lang.ops[1].clone()))
            .plug("OP3", &Workload::new(lang.ops[2].clone()))
            .plug("VAR", &Workload::new(lang.vars.clone()))
            .plug("VAL", &Workload::new(lang.vals.clone()));

        for term in wkld.force() {
            let id = egraph.add_expr(&term.to_string().parse::<RecExpr<HalideLanguage>>().unwrap());
            // TODO: do eval here
        }

        let candidates = cvec_match(&egraph);
    }
}
