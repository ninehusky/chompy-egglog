use chompy::runner::{CVec, Runner};
use egglog::{ast::Expr, Term, Value};
use ruler::recipe_utils::{base_lang, iter_metric, Lang};

struct MathRunner {
    egraph: egglog::EGraph,
    pred_egraph: egglog::EGraph,
    termdag: egglog::TermDag,
    pred_termdag: egglog::TermDag,
    memoized: std::collections::HashMap<Term, CVec<i64>>,
    cvec_len: usize,
}

impl Default for MathRunner {
    fn default() -> Self {
        let mut egraph = egglog::EGraph::default();
        let pred_egraph = egglog::EGraph::default();
        egraph
            .parse_and_run_program(None, include_str!("./egglog/math.egg"))
            .unwrap();
        MathRunner {
            egraph,
            pred_egraph,
            termdag: egglog::TermDag::default(),
            pred_termdag: egglog::TermDag::default(),
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
            .parse_and_run_program(None, &add_command)
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

            // TODO: (@ninehusky):
            // eventually, we'll want to perform some sort of extraction here,
            // to make sure terms which are equivalent aren't unnecessarily added.
            //
            // let (sort, value) = self.egraph.eval_expr(&expr).unwrap();
            // // extract the value
            // let mut termdag = egglog::TermDag::default();
            // self.egraph.extract(value, &mut termdag, &sort);
            // // interpret the value
            self.interpret(expr.clone()).unwrap();
        }
        Ok(String::from("yeah"))
    }

    fn interpret(&mut self, expr: Expr) -> Result<CVec<Self::Constant>, String> {
        let term = self.termdag.expr_to_term(&expr);
        // TODO: would be interesting to see if you could extract out a canonical form here.
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

    fn find_rules(&mut self) -> Vec<chompy::rule::Rule> {
        //     // let's do this the old way, with just cvec matching (non-conditonal)
        //     let mut rules = vec![];
        //     let mut candidate_terms: Vec<egglog::Term> = vec![];
        //     let serialized = self.egraph.serialize(egglog::SerializeConfig::default());
        //     for (cid, class) in serialized.classes() {
        //         // get the representative term.
        //
        //     }
        //     let candidate_terms =
        //     rules
        vec![]
    }
}

// andrew: I can already tell this is going to be a giant clusterfuck.
// basically, here what we'd have to do is (1) get a bunch of rule nodes out of the serialized
// egraph, and then (2) go through each of the rule nodes' children, and extract
// an idea candidate from the lhs and rhs, which we'd have to do through the extraction
// gym or other.
fn _generate_rules(serialized: egraph_serialize::EGraph) {
    let rule_classes: Vec<_> = serialized
        .classes()
        .iter()
        .fold(vec![], |mut acc, (_, class)| {
            // find the nodes with op "rule"
            let nids = class
                .nodes
                .iter()
                .filter(|node| serialized.nodes[*node].op == "Rule")
                .into_iter();
            for nid in nids {
                acc.push(nid);
            }
            acc
        })
        .into_iter()
        .collect();
    println!("found these rules: {:?}", rule_classes);
}

#[test]
fn test_egglog_math() {
    // read the definitions
    const CVEC_LEN: usize = 100;
    let mut egraph = egglog::EGraph::default();
    egraph
        .parse_and_run_program(None, include_str!("./egglog/math.egg"))
        .unwrap();

    let num_cvec = {
        let mut acc = String::from("(Nil)");
        for _ in 0..CVEC_LEN {
            acc = format!("(Cons (Some 0) {})", acc);
        }
        acc
    };

    let var_cvec = {
        let mut acc = String::from("(Nil)");
        for i in 0..CVEC_LEN {
            acc = format!("(Cons (Some {}) {})", i, acc);
        }
        acc
    };

    // generate the rules for cvecs.
    // num:
    egraph
        .parse_and_run_program(
            None,
            &r#"
        (rule
            ((Num ?n))
            ((HasCvec (Num ?n)
                {})))"#
                .replace("{}", &num_cvec),
        )
        .unwrap();

    egraph
        .parse_and_run_program(
            None,
            &r#"
        (rule
            ((Var ?v))
            ((HasCvec (Var ?v)
                {})))"#
                .replace("{}", &var_cvec),
        )
        .unwrap();

    // let's just use Enumo to enumerate the terms.
    let leaves = ruler::enumo::Workload::new(&[
        "(Num 0)",
        "(Num 1)",
        "(Var quoteaquote)",
        "(Var quotebquote)",
    ]);
    let term_language = ruler::enumo::Workload::new(&["EXPR", "(Op2 FN EXPR EXPR)"]).plug(
        "FN",
        &ruler::enumo::Workload::new(&["(Add)", "(Sub)", "(Mul)", "(Div)"]),
    );

    let mut new_language = term_language.clone().plug("EXPR", &leaves);

    for _ in 0..0 {
        new_language = term_language.clone().plug("EXPR", &new_language);
    }

    for (i, term) in new_language.force().into_iter().enumerate() {
        egraph
            .parse_and_run_program(
                None,
                format!("(let term{} {})", i, term.to_string().as_str())
                    .replace("quote", "\"")
                    .as_str(),
            )
            .unwrap();
    }
    egraph.parse_and_run_program(None, "(run 1000000)").unwrap();
    egraph
        .parse_and_run_program(None, "(run cleanup 100000)")
        .unwrap();
}
