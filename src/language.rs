use core::str;
use std::{fmt::Display, ops::Neg};

use ruler::{
    enumo::{Sexp, Workload},
    HashMap,
};

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
    fn eval(&self, env: &HashMap<String, CVec<Self>>) -> CVec<Self>;

    fn make_sexp(&self) -> Sexp;

    fn from_sexp(sexp: Sexp) -> Self
    where
        Self: Sized;

    fn const_type_as_str(&self) -> String;

    /// Returns a list of list of functions of this language. The ith element of the outer list is a list of functions
    /// with arity i.
    /// For example, if a language has two functions, `abs(x)` and `add(x, y)`,
    /// then this function should return `vec![vec![], vec!["abs".to_string()],
    /// vec!["add".to_string()]]`.
    fn get_funcs(&self) -> Vec<Vec<String>>;

    /// Returns a new workload that is the result of applying all
    /// functions to the `old_workload`.
    /// ```
    /// use chompy::language::{ChompyLanguage, MathLang};
    /// use ruler::enumo::Workload;
    /// let lang = MathLang::Var("dummy".to_string());
    /// let old_workload = Workload::new(&["(Var x)".to_string()]);
    /// let new_workload = lang.produce(&old_workload);
    /// let expected: Vec<MathLang> = vec![
    ///     MathLang::Abs(Box::new(MathLang::Var("x".to_string()))),
    ///     MathLang::Neg(Box::new(MathLang::Var("x".to_string()))),
    ///     MathLang::Add(Box::new(MathLang::Var("x".to_string())), Box::new(MathLang::Var("x".to_string()))),
    ///     MathLang::Sub(Box::new(MathLang::Var("x".to_string())), Box::new(MathLang::Var("x".to_string()))),
    ///     MathLang::Mul(Box::new(MathLang::Var("x".to_string())), Box::new(MathLang::Var("x".to_string()))),
    ///     MathLang::Div(Box::new(MathLang::Var("x".to_string())), Box::new(MathLang::Var("x".to_string()))),
    ///  ];
    ///  let actual = new_workload.force().iter().map(|x| MathLang::from_sexp(x.clone())).collect::<Vec<MathLang>>();
    ///  assert_eq!(expected, actual);
    /// ```
    fn produce(&self, old_workload: &Workload) -> Workload {
        let mut result_workload = Workload::empty();
        let funcs = self.get_funcs();
        println!("funcs: {:?}", funcs);
        for arity in 0..funcs.len() {
            let sketch = "(FUNC ".to_string() + &" EXPR ".repeat(arity) + ")";
            println!("arity {} functions are: {:?}", arity, funcs[arity]);
            let funcs = Workload::new(funcs[arity].clone());

            result_workload = Workload::append(
                result_workload,
                Workload::new(&[sketch.to_string()])
                    .plug("FUNC", &funcs)
                    .plug("EXPR", old_workload),
            );
        }
        result_workload
    }

    /// Returns the base set of atoms in the language.
    fn base_atoms(&self) -> Workload {
        let mut atoms = vec![];
        for var in self.get_vars() {
            atoms.push(self.make_var(&var).to_string());
        }
        for val in self.get_vals() {
            atoms.push(self.make_val(val).to_string());
        }
        Workload::new(atoms)
    }

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

#[allow(unused_imports)]
pub mod tests {
    use crate::language::{CVec, ChompyLanguage, Constant};
    use egglog::{sort::EqSort, EGraph};
    use ruler::enumo::Sexp;
    use std::{str::FromStr, sync::Arc};

    #[test]
    // checks that the egglog source code is valid,
    // and that we can construct different terms in some language.
    fn egglog_src_compiles() {
        todo!()
    }
}

/// A generic language for testing purposes.
#[derive(Clone, Debug, PartialEq)]
pub enum MathLang {
    Const(i64),
    Var(String),
    Abs(Box<MathLang>),
    Neg(Box<MathLang>),
    Add(Box<MathLang>, Box<MathLang>),
    Sub(Box<MathLang>, Box<MathLang>),
    Mul(Box<MathLang>, Box<MathLang>),
    Div(Box<MathLang>, Box<MathLang>),
}

impl ChompyLanguage for MathLang {
    type Constant = i64;
    fn get_name(&self) -> String {
        "MathLang".to_string()
    }

    fn get_vals(&self) -> Vec<Self::Constant> {
        vec![1, 2, 3]
    }

    fn get_vars(&self) -> Vec<String> {
        vec!["x".to_string(), "y".to_string(), "z".to_string()]
    }

    fn const_type_as_str(&self) -> String {
        "i64".to_string()
    }

    fn get_funcs(&self) -> Vec<Vec<String>> {
        vec![
            vec![],
            vec!["Abs".to_string(), "Neg".to_string()],
            vec![
                "Add".to_string(),
                "Sub".to_string(),
                "Mul".to_string(),
                "Div".to_string(),
            ],
        ]
    }

    fn make_sexp(&self) -> Sexp {
        match self {
            MathLang::Const(c) => Sexp::List(vec![
                Sexp::Atom("Const".to_string()),
                Sexp::Atom(c.to_string()),
            ]),
            MathLang::Var(v) => Sexp::List(vec![
                Sexp::Atom("Var".to_string()),
                Sexp::Atom(v.to_string()),
            ]),
            MathLang::Abs(e) => Sexp::List(vec![Sexp::Atom("Abs".to_string()), e.make_sexp()]),
            MathLang::Neg(e) => Sexp::List(vec![Sexp::Atom("Neg".to_string()), e.make_sexp()]),
            MathLang::Add(e1, e2) => Sexp::List(vec![
                Sexp::Atom("Add".to_string()),
                e1.make_sexp(),
                e2.make_sexp(),
            ]),
            MathLang::Sub(e1, e2) => Sexp::List(vec![
                Sexp::Atom("Sub".to_string()),
                e1.make_sexp(),
                e2.make_sexp(),
            ]),
            MathLang::Mul(e1, e2) => Sexp::List(vec![
                Sexp::Atom("Mul".to_string()),
                e1.make_sexp(),
                e2.make_sexp(),
            ]),
            MathLang::Div(e1, e2) => Sexp::List(vec![
                Sexp::Atom("Div".to_string()),
                e1.make_sexp(),
                e2.make_sexp(),
            ]),
        }
    }

    fn from_sexp(sexp: Sexp) -> Self
    where
        Self: Sized,
    {
        match sexp {
            Sexp::List(l) => {
                let op = l[0].to_string();
                match op.as_str() {
                    "Const" => MathLang::Const(l[1].to_string().parse().unwrap()),
                    "Var" => MathLang::Var(l[1].to_string()),
                    "Abs" => MathLang::Abs(Box::new(MathLang::from_sexp(l[1].clone()))),
                    "Neg" => MathLang::Neg(Box::new(MathLang::from_sexp(l[1].clone()))),
                    "Add" => MathLang::Add(
                        Box::new(MathLang::from_sexp(l[1].clone())),
                        Box::new(MathLang::from_sexp(l[2].clone())),
                    ),
                    "Sub" => MathLang::Sub(
                        Box::new(MathLang::from_sexp(l[1].clone())),
                        Box::new(MathLang::from_sexp(l[2].clone())),
                    ),
                    "Mul" => MathLang::Mul(
                        Box::new(MathLang::from_sexp(l[1].clone())),
                        Box::new(MathLang::from_sexp(l[2].clone())),
                    ),
                    "Div" => MathLang::Div(
                        Box::new(MathLang::from_sexp(l[1].clone())),
                        Box::new(MathLang::from_sexp(l[2].clone())),
                    ),
                    _ => unreachable!(),
                }
            }
            _ => unreachable!(),
        }
    }

    fn eval(&self, env: &HashMap<String, CVec<Self>>) -> CVec<Self> {
        match self {
            MathLang::Const(c) => vec![Some(*c)],
            MathLang::Var(v) => env[v].clone(),
            MathLang::Abs(e) => {
                let e: CVec<Self> = e.eval(env);
                e.into_iter()
                    .map(|x| if let Some(x) = x { Some(x.abs()) } else { None })
                    .collect()
            }
            MathLang::Neg(e) => {
                let e = e.eval(env);
                e.into_iter()
                    .map(|x| if let Some(x) = x { Some(x.neg()) } else { None })
                    .collect()
            }
            MathLang::Add(e1, e2)
            | MathLang::Sub(e1, e2)
            | MathLang::Mul(e1, e2)
            | MathLang::Div(e1, e2) => {
                let e1 = e1.eval(env);
                let e2 = e2.eval(env);
                let f = |(x, y): (Option<Self::Constant>, Option<Self::Constant>)| {
                    if x.is_none() || y.is_none() {
                        return None;
                    }
                    let x = x.unwrap();
                    let y = y.unwrap();
                    match self {
                        MathLang::Add(_, _) => x.checked_add(y),
                        MathLang::Sub(_, _) => x.checked_sub(y),
                        MathLang::Mul(_, _) => x.checked_mul(y),
                        MathLang::Div(_, _) => x.checked_div(y),
                        _ => unreachable!(),
                    }
                };
                e1.into_iter()
                    .zip(e2.into_iter())
                    .map(|(x, y)| f((x, y)))
                    .collect()
            }
        }
    }
}
