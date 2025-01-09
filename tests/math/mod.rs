pub mod tests {
    use chompy::{
        chomper::{Chomper, MathChomper, Rule},
        language::{ChompyLanguage, MathLang},
    };
    use ruler::enumo::Sexp;
    use std::str::FromStr;

    use super::super::evaluate_ruleset;

    #[test]
    fn check_math_rules() {
        let chomper = MathChomper;
        let predicates = chomper.get_language().get_predicates();
        let values = chomper.get_language().get_vals();
        for v in values {
            println!("Value: {}", chomper.get_language().make_val(v));
        }
        for p in predicates.force() {
            println!("Predicate: {}", p);
        }
        let rules = chomper.run_chompy(5);
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
}

