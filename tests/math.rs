use chompy::{language::*, runner::Runner};
use egglog::ast::Command;
use ruler::HashMap;
use std::fmt::Display;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum MathLang {
    Num(i64),
    Var(String),
    Add(Box<MathLang>, Box<MathLang>),
    Sub(Box<MathLang>, Box<MathLang>),
    Mul(Box<MathLang>, Box<MathLang>),
    Div(Box<MathLang>, Box<MathLang>),
}

impl ChompyLang for MathLang {
    type Constant = i64;

    fn parse(statement: &str) -> Self {
        assert!(statement.starts_with("(") && statement.ends_with(")"));
        // get the first token
        let mut tokens = statement[1..statement.len() - 1].split_whitespace();
        let operator = tokens.next().unwrap();
        let children = MathLang::_get_children(statement);
        match operator {
            "Num" => MathLang::Num(children[0].parse().unwrap()),
            "Var" => MathLang::Var(children[0].clone()),
            _ => {
                let left = Box::new(MathLang::parse(&children[0]));
                let right = Box::new(MathLang::parse(&children[1]));
                match operator {
                    "Add" => MathLang::Add(left, right),
                    "Sub" => MathLang::Sub(left, right),
                    "Mul" => MathLang::Mul(left, right),
                    "Div" => MathLang::Div(left, right),
                    _ => panic!("Unknown operator: {}", operator),
                }
            }
        }
    }

    fn to_sexpr(&self) -> String {
        match self {
            MathLang::Num(n) => format!("(Num {})", n),
            MathLang::Var(v) => format!("(Var \"{}\")", v),
            MathLang::Add(l, r) => format!("(Add {} {})", l.to_sexpr(), r.to_sexpr()),
            MathLang::Sub(l, r) => format!("(Sub {} {})", l.to_sexpr(), r.to_sexpr()),
            MathLang::Mul(l, r) => format!("(Mul {} {})", l.to_sexpr(), r.to_sexpr()),
            MathLang::Div(l, r) => format!("(Div {} {})", l.to_sexpr(), r.to_sexpr()),
        }
    }
}

impl Display for MathLang {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_sexpr())
    }
}

pub struct MathRunner {
    egraph: egglog::EGraph,
    memoized: HashMap<MathLang, CVec<MathLang>>,
    cvec_len: usize,
    expr_num: usize,
}

impl Default for MathRunner {
    fn default() -> Self {
        let mut egraph = egglog::EGraph::default();
        egraph
            .parse_and_run_program(include_str!("../src/egglog_src/math.egg"))
            .unwrap();
        MathRunner {
            egraph,
            memoized: HashMap::default(),
            cvec_len: 3,
            expr_num: 0,
        }
    }
}

impl Runner<MathLang> for MathRunner {
    /// one important thing to note is that the only exprs which are added
    /// to the egraph are those outlined in terms.
    /// for example, if a term we're trying to add is `(Add (Num 1) (Num 1))`,
    /// we will add the outerlying add to the egraph, but the inner nums won't
    /// be (even though they will be added to the memoized hashmap).
    fn add_terms(&mut self, terms: Vec<MathLang>) -> Result<String, String> {
        for term in terms {
            if let Some(_) = self.memoized.get(&term) {
                continue;
            }
            let cvec = self.interpret(term.clone())?;
            let cvec_str = MathLang::cvec_to_sexpr(&cvec);

            let add_cmd = format!("(let expr{} {})", self.expr_num, term.to_sexpr());
            // now, we r rdy 2 add tha cvec 2 tha egraff :D
            let my_str = format!("(set (HasCvec expr{}) {})", self.expr_num, cvec_str);

            self.expr_num += 1;

            let prog = format!("{}\n{}", add_cmd, my_str);
            println!("{}", prog);
            self.egraph.parse_and_run_program(&prog).unwrap();
        }
        Ok(String::from("Success!"))
    }

    fn interpret(&mut self, term: MathLang) -> Result<CVec<MathLang>, String> {
        if let Some(cvec) = self.memoized.get(&term) {
            return Ok(cvec.clone());
        }
        // well, now we gotta do some work!
        let result = Ok(match term.clone() {
            // should be cvec of size cvec_len
            MathLang::Num(n) => vec![Some(n); self.cvec_len],
            MathLang::Var(_) => (0..self.cvec_len)
                .into_iter()
                .map(|x| Some(x.try_into().unwrap()))
                .collect(),
            MathLang::Add(l, r)
            | MathLang::Sub(l, r)
            | MathLang::Mul(l, r)
            | MathLang::Div(l, r) => {
                let f = match term {
                    MathLang::Add(..) => i64::checked_add,
                    MathLang::Sub(..) => i64::checked_sub,
                    MathLang::Mul(..) => i64::checked_mul,
                    MathLang::Div(..) => i64::checked_div,
                    _ => unreachable!(),
                };

                let l_cvec = self.interpret(*l)?;
                let r_cvec = self.interpret(*r)?;
                l_cvec
                    .iter()
                    .zip(r_cvec.iter())
                    .map(|(l, r)| match (l, r) {
                        (Some(l), Some(r)) => f(*l, *r),
                        _ => None,
                    })
                    .collect()
            }
        });
        match &result {
            Ok(cvec) => {
                self.memoized.insert(term, cvec.clone());
            }
            Err(_) => {}
        }
        result
    }
}

#[test]
fn test() {
    let prog = MathLang::parse("(Add (Var x) (Mul (Num 234) (Num 239487)))");
    println!("{:?}", prog);
    let mut runner = MathRunner::default();
    let terms = vec!["(Num 1)", "(Var x)", "(Add (Num 1) (Num 2))"];
    runner
        .add_terms(terms.into_iter().map(|x| MathLang::parse(x)).collect())
        .unwrap();
}
