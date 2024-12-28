use core::str;
use std::fmt::Display;

use ruler::{enumo::Sexp, HashMap};

pub type Constant<L> = <L as ChompyLanguage>::Constant;
pub type CVec<L> = Vec<Option<Constant<L>>>;

/// An interface for languages.
pub trait ChompyLanguage {
    type Constant: Display + Clone;
    /// Returns the name of the language.
    /// This will also be the name of the top-level `datatype`
    /// defining the language in the Egglog source.
    fn get_name(&self) -> String;

    /// Returns the variables that Chompy will take to infer equalities.
    fn get_vars(&self) -> Vec<String>;

    /// Returns the initial set of constants that Chompy will use to infer equalities.
    fn get_vals(&self) -> Vec<Constant<Self>>;

    /// Interprets the given term in the given environment.
    fn eval(&self, sexp: &Sexp, env: &HashMap<String, CVec<Self>>) -> CVec<Self>;

    fn const_type_as_str(&self) -> String;

    /// Returns a list of list of functions of this language. The ith element of the outer list is a list of functions
    /// with arity i.
    /// For example, if a language has two functions, `abs(x)` and `add(x, y)`,
    /// then this function should return `vec![vec![], vec!["abs".to_string()],
    /// vec!["add".to_string()]]`.
    fn get_funcs(&self) -> Vec<Vec<String>>;

    /// Constructs a variable in the language with the given id.
    fn make_var(&self, id: &str) -> Sexp {
        Sexp::List(vec![
            Sexp::Atom("Var".to_string()),
            Sexp::Atom(id.to_string()),
        ])
    }

    /// Constructs a value (constant) in the language with the given id.
    /// See `make_var` for an example.
    fn make_val(&self, val: Constant<Self>) -> Sexp {
        Sexp::List(vec![
            Sexp::Atom("Const".to_string()),
            Sexp::Atom(val.to_string()),
        ])
    }

    /// Returns the Egglog source code which defines this language.
    fn to_egglog_src(&self) -> String {
        let name = self.get_name();

        // build the function definitions.
        let mut func_defs: Vec<String> = vec![];

        let funcs = self.get_funcs();

        for arity in 0..funcs.len() {
            for func in &funcs[arity] {
                let mut defn = format!("(function {func} (");
                for _ in 0..arity {
                    defn += format!("{name} ").as_str();
                }
                defn += &format!(") {name})").to_string();
                func_defs.push(defn);
            }
        }

        let func_defs_str = func_defs.join("\n");
        let const_type = self.const_type_as_str();

        let src = format!(
            r#"
(function Const ({const_type}) {name})
(function Var (String) {name})
{func_defs_str}
(function eclass ({name}) i64 :merge (min old new))
(relation universe ({name}))
(relation cond-equal ({name} {name}))

;;; forward ruleset definitions
(ruleset eclass-report)
(ruleset non-cond-rewrites)
(ruleset cond-rewrites)

;;; a "function", more or less, that prints out each e-class and its
;;; term.
;;; i'm not 100% sure why this only runs once per e-class -- it's because
;;; the (eclass ?term) can only be matched on once?
(rule ((eclass ?term)) ((extract "eclass:") (extract (eclass ?term)) (extract "candidate term:") (extract ?term)) :ruleset eclass-report)
        "#
        );
        src.to_string()
    }
}

pub mod tests {
    use crate::language::{CVec, ChompyLanguage, Constant};
    use egglog::{sort::EqSort, EGraph};
    use ruler::enumo::Sexp;
    use std::{str::FromStr, sync::Arc};

    #[derive(Clone)]
    pub struct MathLang;

    impl ChompyLanguage for MathLang {
        type Constant = i64;

        fn get_name(&self) -> String {
            "Math".to_string()
        }

        fn const_type_as_str(&self) -> String {
            "i64".to_string()
        }

        fn get_vars(&self) -> Vec<String> {
            vec!["x".to_string(), "y".to_string()]
        }

        fn get_vals(&self) -> Vec<Self::Constant> {
            vec![1, 2, 3]
        }

        fn eval(&self, sexp: &Sexp, env: &ruler::HashMap<String, CVec<Self>>) -> CVec<Self> {
            todo!()
        }

        fn get_funcs(&self) -> Vec<Vec<String>> {
            vec![vec![], vec!["Abs".to_string()], vec!["Add".to_string()]]
        }
    }

    #[test]
    // checks that the egglog source code is valid,
    // and that we can construct different terms in some language.
    fn egglog_src_compiles() {
        let lang = MathLang;
        let src = lang.to_egglog_src();
        let mut egraph = EGraph::default();
        let math_sort = Arc::new(EqSort {
            // name: lang.get_name().into(),
            name: "Math".into(),
        });
        egraph.add_arcsort(math_sort.clone()).unwrap();
        println!("the source:");
        println!("{}", src);
        egraph.parse_and_run_program(None, &src).unwrap();
        egraph
            .parse_and_run_program(None, "(Abs (Var \"x\"))")
            .unwrap();
        egraph
            .parse_and_run_program(None, "(Add (Var \"x\") (Var \"x\"))")
            .unwrap();
        egraph
            .parse_and_run_program(None, "(check (Abs (Var \"x\")))")
            .unwrap();
        egraph
            .parse_and_run_program(None, "(check (Add (Var \"x\") (Var \"x\")))")
            .unwrap();
    }
}
