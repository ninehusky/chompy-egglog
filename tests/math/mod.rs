use chompy::{
    chomper::{Chomper, MathChomper},
    language::{ChompyLanguage, MathLang},
};
use ruler::enumo::Workload;

pub mod tests {
    use chompy::{
        chomper::{Chomper, MathChomper, Rule},
        language::{ChompyLanguage, MathLang},
    };
    use ruler::enumo::Sexp;
    use std::str::FromStr;

    use super::{
        super::evaluate_ruleset, MiddleSchoolLangChomper, MiddleSchoolLangConditionsChomper,
    };

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
        let rules = chomper.run_chompy(7);
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

    // #[test]
    // fn middle_school_total_tests() {
    //     let chomper = MiddleSchoolLangChomper {
    //         math_chomper: MathChomper,
    //     };
    //     chomper.run_chompy(6);
    // }

    // #[test]
    // fn middle_school_conditional_tests() {
    //     let chomper = MiddleSchoolLangConditionsChomper {
    //         math_chomper: MathChomper,
    //     };
    //     chomper.run_chompy(8);
    // }
}

pub struct MiddleSchoolLang {
    pub math_lang: MathLang,
}

impl ChompyLanguage for MiddleSchoolLang {
    type Constant = i64;

    fn get_name(&self) -> String {
        self.math_lang.get_name()
    }

    fn get_vars(&self) -> Vec<String> {
        self.math_lang.get_vars()
    }

    fn get_vals(&self) -> Vec<chompy::language::Constant<Self>> {
        self.math_lang.get_vals()
    }

    fn const_to_bool(&self, val: chompy::language::Constant<Self>) -> bool {
        self.math_lang.const_to_bool(val)
    }

    fn get_funcs(&self) -> Vec<Vec<String>> {
        vec![
            vec![],
            vec!["Abs".into()],
            vec!["Add".into(), "Sub".into(), "Mul".into(), "Div".into()],
        ]
    }

    fn validate_rule(&self, rule: &chompy::chomper::Rule) -> chompy::language::ValidationResult {
        self.math_lang.validate_rule(rule)
    }

    fn concretize_rule(
        &self,
        rule: &chompy::chomper::Rule,
        env_cache: &mut ruler::HashMap<
            (String, String),
            Vec<ruler::HashMap<String, ruler::enumo::Sexp>>,
        >,
    ) -> Vec<(ruler::enumo::Sexp, ruler::enumo::Sexp)> {
        self.math_lang.concretize_rule(rule, env_cache)
    }

    fn const_type_as_str(&self) -> String {
        self.math_lang.const_type_as_str()
    }

    fn make_sexp(&self) -> ruler::enumo::Sexp {
        self.math_lang.make_sexp()
    }

    fn make_var(&self, name: &str) -> ruler::enumo::Sexp {
        self.math_lang.make_var(name)
    }

    fn eval(
        &self,
        sexp: &ruler::enumo::Sexp,
        env: &ruler::HashMap<String, chompy::language::CVec<Self>>,
    ) -> chompy::language::CVec<Self> {
        self.math_lang.eval(sexp, env)
    }

    fn get_predicates(&self) -> ruler::enumo::Workload {
        Workload::empty()
    }
}

pub struct MiddleSchoolLangChomper {
    pub math_chomper: MathChomper,
}

impl Chomper for MiddleSchoolLangChomper {
    type Constant = i64;
    fn initialize_env(
        &self,
    ) -> ruler::HashMap<String, chompy::language::CVec<dyn ChompyLanguage<Constant = Self::Constant>>>
    {
        self.math_chomper.initialize_env()
    }

    fn make_pred_interpreter() -> impl chompy::PredicateInterpreter + 'static {
        MathChomper::make_pred_interpreter()
    }

    fn get_initial_egraph(&self) -> egglog::EGraph {
        self.math_chomper.get_initial_egraph()
    }

    fn get_language(&self) -> Box<impl ChompyLanguage<Constant = Self::Constant>> {
        Box::new(MiddleSchoolLang {
            math_lang: MathLang::Var("dummy".into()),
        })
    }
}

pub struct MiddleSchoolLangConditions {
    pub math_lang: MathLang,
}

impl ChompyLanguage for MiddleSchoolLangConditions {
    type Constant = i64;

    fn get_name(&self) -> String {
        self.math_lang.get_name()
    }

    fn get_vars(&self) -> Vec<String> {
        self.math_lang.get_vars()
    }

    fn get_vals(&self) -> Vec<chompy::language::Constant<Self>> {
        self.math_lang.get_vals()
    }

    fn const_to_bool(&self, val: chompy::language::Constant<Self>) -> bool {
        self.math_lang.const_to_bool(val)
    }

    fn get_funcs(&self) -> Vec<Vec<String>> {
        vec![
            vec![],
            vec!["Abs".into()],
            vec!["Add".into(), "Sub".into(), "Mul".into(), "Div".into()],
        ]
    }

    fn validate_rule(&self, rule: &chompy::chomper::Rule) -> chompy::language::ValidationResult {
        self.math_lang.validate_rule(rule)
    }

    fn concretize_rule(
        &self,
        rule: &chompy::chomper::Rule,
        env_cache: &mut ruler::HashMap<
            (String, String),
            Vec<ruler::HashMap<String, ruler::enumo::Sexp>>,
        >,
    ) -> Vec<(ruler::enumo::Sexp, ruler::enumo::Sexp)> {
        self.math_lang.concretize_rule(rule, env_cache)
    }

    fn const_type_as_str(&self) -> String {
        self.math_lang.const_type_as_str()
    }

    fn make_sexp(&self) -> ruler::enumo::Sexp {
        self.math_lang.make_sexp()
    }

    fn make_var(&self, name: &str) -> ruler::enumo::Sexp {
        self.math_lang.make_var(name)
    }

    fn eval(
        &self,
        sexp: &ruler::enumo::Sexp,
        env: &ruler::HashMap<String, chompy::language::CVec<Self>>,
    ) -> chompy::language::CVec<Self> {
        self.math_lang.eval(sexp, env)
    }

    fn get_predicates(&self) -> ruler::enumo::Workload {
        let atoms: Vec<String> = self
            .get_vals()
            .into_iter()
            .map(|val| self.make_val(val))
            .chain(self.get_vars().iter().map(|var| self.make_var(var)))
            .map(|atom| atom.to_string())
            .collect();

        Workload::new(&["(BINOP EXPR EXPR)"])
            .plug("BINOP", &Workload::new(&["Neq", "Gt"]))
            .plug("EXPR", &Workload::new(atoms))
    }
}

pub struct MiddleSchoolLangConditionsChomper {
    pub math_chomper: MathChomper,
}

impl Chomper for MiddleSchoolLangConditionsChomper {
    type Constant = i64;
    fn initialize_env(
        &self,
    ) -> ruler::HashMap<String, chompy::language::CVec<dyn ChompyLanguage<Constant = Self::Constant>>>
    {
        self.math_chomper.initialize_env()
    }

    fn make_pred_interpreter() -> impl chompy::PredicateInterpreter + 'static {
        MathChomper::make_pred_interpreter()
    }

    fn get_initial_egraph(&self) -> egglog::EGraph {
        self.math_chomper.get_initial_egraph()
    }

    fn get_language(&self) -> Box<impl ChompyLanguage<Constant = Self::Constant>> {
        Box::new(MiddleSchoolLangConditions {
            math_lang: MathLang::Var("dummy".into()),
        })
    }
}
