pub mod tests {
    use chompy::{
        chomper::{Chomper, MathChomper, Rule},
        language::{ChompyLanguage, MathLang},
    };
    use ruler::enumo::Sexp;
    use std::str::FromStr;

    use super::super::evaluate_ruleset;

    pub const PYTHON_GPT_SCRIPT_PATH: &str = "python/query_gpt.py";

    #[test]
    fn check_math_rules() {
        env_logger::init();
        let chomper = MathChomper;
        let predicates = chomper.get_language().get_predicates();
        let values = chomper.get_language().get_vals();
        for v in values {
            println!("Value: {}", chomper.get_language().make_val(v));
        }
        for p in predicates.force() {
            println!("Predicate: {}", p);
        }
        let rules = chomper.run_chompy(8);
        let hand_picked_rules = vec![
            Rule {
                condition: Sexp::from_str("(Neq ?x (Const 0))").ok(),
                lhs: Sexp::from_str("(Div ?x ?x)").unwrap(),
                rhs: Sexp::from_str("(Const 1)").unwrap(),
            },
            Rule {
                condition: Sexp::from_str("(Gt ?x (Const -1))").ok(),
                lhs: Sexp::from_str("(Abs ?x)").unwrap(),
                rhs: Sexp::from_str("?x").unwrap(),
            },
        ];
        evaluate_ruleset::<MathChomper, MathLang>(
            &rules,
            &hand_picked_rules,
            chomper,
            MathLang::Var("dummy".into()),
        );
    }

    /// Chompy vs. ChatGPT.
    /// Generates a set of rules with Chompy and compares them with GPT.
    /// TODO: output some sort of json/other format to compare.
    #[test]
    fn check_against_llm() {
        let chomper = MathChomper;
        let rules = chomper.run_chompy(2);
        let proc = std::process::Command::new("python3")
            .arg(PYTHON_GPT_SCRIPT_PATH)
            .output()
            .expect("failed to execute process");

        let stderr = String::from_utf8_lossy(&proc.stderr);

        println!("stderr: {}", stderr);

        assert!(proc.status.success());

        println!("chompy rules: {}", rules.len());

        let stdout = String::from_utf8_lossy(&proc.stdout);

        let mut egraph = chomper.get_initial_egraph();
        for rule in rules {
            chomper.add_rewrite(&mut egraph, &rule);
        }

        // throw away first two lines from stdout:
        for line in stdout.lines().skip(2) {
            let rule: Result<Rule, _> = line.try_into();

            if let Ok(ref rule) = rule {
                println!("ChatGPT rule: {}", rule);
                // try to parse the rule as MathLang
                let lhs_result: Result<MathLang, String> = rule.lhs.clone().try_into();
                if let Ok(lhs) = lhs_result {
                    println!("lhs: {:?}", lhs);
                } else {
                    println!("lhs unparsable: {:?}", lhs_result);
                    continue;
                }

                let rhs_result: Result<MathLang, String> = rule.rhs.clone().try_into();
                if let Ok(rhs) = rhs_result {
                    println!("rhs: {:?}", rhs);
                } else {
                    println!("rhs unparsable");
                    continue;
                }

                if let Some(ref cond) = rule.condition {
                    let cond_result: Result<MathLang, String> = cond.clone().try_into();
                    if let Ok(cond) = cond_result {
                        println!("condition: {:?}", cond);
                    } else {
                        println!("condition unparsable");
                        continue;
                    }
                }

                if chomper.rule_is_derivable(&egraph, &rule, &mut Default::default()) {
                    println!("Rule is derivable");
                } else {
                    println!("Rule is not derivable");
                }
            }

            match rule {
                Ok(rule) => {
                    println!("ChatGPT rule: {}", rule);
                    if chomper.rule_is_derivable(&egraph, &rule, &mut Default::default()) {
                        println!("Rule is derivable");
                    } else {
                        println!("Rule is not derivable");
                    }
                }
                Err(e) => {
                    println!("error unparsable: {}", e);
                }
            }
        }
    }
}
