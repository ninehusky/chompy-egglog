// like math, but using egglog bindings where i can.
//
use chompy::runner::{CVec, Runner};
use egglog::{ast::Expr, Term};

struct MathRunner {
    egraph: egglog::EGraph,
    termdag: egglog::TermDag,
    memoized: std::collections::HashMap<Term, CVec<i64>>,
    cvec_len: usize,
}

impl Default for MathRunner {
    fn default() -> Self {
        let mut egraph = egglog::EGraph::default();
        egraph
            .parse_and_run_program(include_str!("./egglog/math.egg"))
            .unwrap();
        MathRunner {
            egraph,
            termdag: egglog::TermDag::default(),
            memoized: std::collections::HashMap::default(),
            cvec_len: 5,
        }
    }
}

impl MathRunner {
    fn _add_term_to_egraph(&mut self, expr: Expr) -> Result<Vec<String>, String> {
        let term = self.termdag.expr_to_term(&expr);
        assert!(
            self.memoized.get(&term).is_some(),
            "interpret the expr {} and memoize it!\nmemoized is {:?}\n{:?}.",
            expr.to_sexp(),
            self.memoized,
            term
        );
        let expr_id = format!("expr{}", self.memoized.len());
        let add_command = format!("(let {} {})", expr_id, expr.to_sexp());
        self.egraph
            .parse_and_run_program(&add_command)
            .map_err(|e| e.to_string())
    }
}

impl Runner for MathRunner {
    type Constant = i64;

    fn add_exprs(&mut self, exprs: Vec<Expr>) -> Result<String, String> {
        // convert the expr to a term.
        for expr in exprs {
            let term = self.termdag.expr_to_term(&expr);

            if let Some(_) = self.memoized.get(&term) {
                continue;
            }

            // let (sort, value) = self.egraph.eval_expr(&expr).unwrap();
            // // extract the value
            // let mut termdag = egglog::TermDag::default();
            // self.egraph.extract(value, &mut termdag, &sort);
            // // interpret the value
            self.interpret(expr.clone()).unwrap();
        }
        Ok(String::from("yeah"))
    }

    fn interpret(&mut self, expr: Expr) -> Result<chompy::runner::CVec<Self::Constant>, String> {
        let term = self.termdag.expr_to_term(&expr);
        if let Some(cvec) = self.memoized.get(&term) {
            return Ok(cvec.clone());
        }
        // now we gotta interpret the expr.
        let cvec = match expr.clone() {
            Expr::Lit(_, _) => Err("You shouldn't be interpreting a literal".to_string()),
            Expr::Var(_, _) => Err(
                "You shouldn't be interpreting a variable directly, it should be (Var blah)"
                    .to_string(),
            ),
            Expr::Call(_, f, args) => match args.len() {
                1 => match f.as_str() {
                    "Num" => {
                        let num = match args[0].clone() {
                            Expr::Lit(_, egglog::ast::Literal::Int(i)) => i,
                            _ => return Err("Expected a number".to_string()),
                        };
                        Ok(vec![Some(num); self.cvec_len])
                    }
                    "Var" => {
                        match args[0].clone() {
                            Expr::Lit(_, egglog::ast::Literal::String(_)) => (),
                            _ => {
                                return Err(format!(
                                    "expected a string, but got {}",
                                    args[0].to_sexp()
                                ))
                            }
                        };
                        Ok((0..self.cvec_len)
                            .into_iter()
                            .map(|x| Some(x.try_into().unwrap()))
                            .collect())
                    }
                    _ => return Err(format!("Unknown function {}", f)),
                },
                2 => {
                    let func = match f.as_str() {
                        "Add" => i64::checked_add,
                        "Sub" => i64::checked_sub,
                        "Mul" => i64::checked_mul,
                        "Div" => i64::checked_div,
                        _ => return Err(format!("Unknown function {}", f)),
                    };
                    let l_cvec = self.interpret(args[0].clone())?;
                    let r_cvec = self.interpret(args[1].clone())?;
                    Ok(l_cvec
                        .iter()
                        .zip(r_cvec.iter())
                        .map(|(l, r)| match (l, r) {
                            (Some(l), Some(r)) => func(*l, *r),
                            _ => None,
                        })
                        .collect())
                }
                _ => Err("Unknown number of arguments".to_string()),
            },
        };
        // put the expr in the hashmap.
        self.memoized
            .insert(self.termdag.expr_to_term(&expr), cvec.clone().unwrap());
        // add it to the egraph.
        self._add_term_to_egraph(expr).unwrap();
        cvec
    }

    fn find_rules(&self, cvecs: &CVec<Self::Constant>) -> Vec<chompy::rule::Rule> {
        vec![]
    }
}

#[test]
fn test_egglog_math() {
    // read the definitions
    let mut egraph = egglog::EGraph::default();
    egraph
        .parse_and_run_program(include_str!("./egglog/math.egg"))
        .unwrap();
    let mut runner = MathRunner::default();
    let sexprs = vec!["(Num 1)", "(Div (Var \"x\") (Var \"x\"))"];

    let parser = egglog::ast::parse::ExprParser::new();
    runner
        .add_exprs(sexprs.iter().map(|x| parser.parse(x).unwrap()).collect())
        .unwrap();
}
