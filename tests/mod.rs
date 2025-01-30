use chompy::chomper::{Chomper, Rule};
use chompy::language::ChompyLanguage;
use ruler::enumo::Sexp;

// mod halide;
mod math;

// This is a hack. `rule_is_derivable` calls
// `concretize_rule`, which expects the rules which are
// discovered via observational equivalence, i.e., rules
// before they have been generalized. Going down a level, this
// means `concretize_rule` expects the rules to have variables
// as `(Var blah)` vs. what gets output by Chompy, which is
// `?blah`. This function transforms the rules from the latter
// format to the former.
pub fn transform_rule(rule: &Rule, language: &Box<impl ChompyLanguage>) -> Rule {
    fn transform_sexp(sexp: &Sexp, language: &Box<impl ChompyLanguage>) -> Sexp {
        match sexp {
            Sexp::Atom(a) => {
                if a.starts_with("?") {
                    language.make_var(&a[1..])
                } else {
                    sexp.clone()
                }
            }
            Sexp::List(l) => Sexp::List(l.iter().map(|s| transform_sexp(s, language)).collect()),
        }
    }
    Rule {
        condition: if let Some(cond) = &rule.condition {
            Some(transform_sexp(cond, language))
        } else {
            None
        },
        lhs: transform_sexp(&rule.lhs, language),
        rhs: transform_sexp(&rule.rhs, language),
    }
}

pub fn evaluate_ruleset<C: Chomper + Sized, L: ChompyLanguage + Sized>(
    chompy_rules: &Vec<Rule>,
    other_rules: &Vec<Rule>,
    chomper: C,
    language: L,
) {
    let mut egraph = chomper.get_initial_egraph();
    for r in chompy_rules {
        chomper.add_rewrite(&mut egraph, r);
    }

    let b = Box::new(language);
    for rule in other_rules {
        let rule = transform_rule(rule, &b);
        let result = chomper.rule_is_derivable(&egraph, &rule);
        if result {
            println!("Rule is derivable: {:?}", rule);
        } else {
            println!("Rule is not derivable: {:?}", rule);
        }
    }
}
