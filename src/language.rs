use core::str;
use std::{collections::HashSet, fmt::Display, ops::Neg};

use rand::rngs::StdRng;
use rand::Rng;
use ruler::{
    enumo::{Sexp, Workload},
    HashMap,
};

use log::info;

use z3::ast::Ast;

use crate::chomper::Rule;

pub type Constant<L> = <L as ChompyLanguage>::Constant;
pub type CVec<L> = Vec<Option<Constant<L>>>;

#[derive(Debug, PartialEq)]
pub enum ValidationResult {
    Valid,
    Invalid,
    Unknown,
}

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

    /// Returns a Workload containing conditions for the language.
    fn get_predicates(&self) -> Workload;

    /// Interprets the given term in the given environment.
    fn eval(&self, sexp: &Sexp, env: &HashMap<String, CVec<Self>>) -> CVec<Self>;

    fn make_sexp(&self) -> Sexp;

    fn const_type_as_str(&self) -> String;

    /// Given some rule `(l, r)`, returns a vector of `(l', r')` pairs where `l'` and `r'`
    /// are `l` and `r` concretized with variables replaced by constants. `l'` must be
    /// equivalent to `r'`.
    fn concretize_rule(&self, rule: &Rule) -> Vec<(Sexp, Sexp)>;

    fn generalize_term(&self, cache: &mut HashMap<String, String>, term: &Sexp) -> Sexp {
        fn letter(i: usize) -> char {
            (b'a' + (i % 26) as u8) as char
        }

        if is_var(term) {
            let var = term.to_string();
            if let Some(v) = cache.get(&var) {
                return Sexp::Atom(v.clone());
            }
            let v = letter(cache.len());
            let id = format!("?{}", v);
            cache.insert(var, id.clone());
            return Sexp::Atom(id);
        }

        match term {
            Sexp::Atom(_) => term.clone(),
            Sexp::List(l) => {
                let mut new_l: Vec<Sexp> = vec![];
                for t in l {
                    new_l.push(self.generalize_term(cache, t));
                }
                Sexp::List(new_l)
            }
        }
    }

    fn generalize_rule(&self, rule: &Rule) -> Rule {
        let mut cache = Default::default();
        let l = self.generalize_term(&mut cache, &rule.lhs);
        let r = self.generalize_term(&mut cache, &rule.rhs);
        if let Some(cond) = &rule.condition {
            let cond = self.generalize_term(&mut cache, cond);
            Rule {
                lhs: l,
                rhs: r,
                condition: Some(cond),
            }
        } else {
            Rule {
                lhs: l,
                rhs: r,
                condition: rule.condition.clone(),
            }
        }
    }

    /// Determines whether the given rule is valid in the language.
    /// If this function returns `ValidationResult::Valid`, then for a non-conditional rule `l ~>
    /// r`, `l = r` in the language.
    /// For a conditional rule `if c then l ~> r`, if `c` is true in the language, then `l = r`,
    /// i.e., `c -> l = r`.
    fn validate_rule(&self, rule: &Rule) -> ValidationResult;

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
        for arity in 0..funcs.len() {
            let sketch = "(FUNC ".to_string() + &" EXPR ".repeat(arity) + ")";
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

    /// Converts a `Constant` in the language to a `bool`.
    fn const_to_bool(&self, val: Constant<Self>) -> bool;

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

/// Helper function which returns whether the given
/// s-expression is a variable.
/// ```
/// use ruler::enumo::Sexp;
/// use std::str::FromStr;
/// assert!(is_var(Sexp::from_str("(Var blah)")));
/// assert!(!is_var(Sexp::from_str("(Const blah)")));
/// assert!(!is_var(Sexp::from_str("(var blah)")));
/// ```
fn is_var(sexp: &Sexp) -> bool {
    match sexp {
        Sexp::List(l) => {
            if l.len() != 2 {
                return false;
            }
            if let Sexp::Atom(a) = &l[0] {
                return a == "Var";
            }
            false
        }
        _ => false,
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

// This is a sample implementation of the ChompyLanguage trait.
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
    // conditions
    Gt(Box<MathLang>, Box<MathLang>),
    Neq(Box<MathLang>, Box<MathLang>),
}

impl From<Sexp> for MathLang {
    fn from(sexp: Sexp) -> Self {
        match sexp {
            Sexp::List(l) => {
                let op = l[0].to_string();
                match op.as_str() {
                    "Const" => MathLang::Const(l[1].to_string().parse().unwrap()),
                    "Var" => MathLang::Var(l[1].to_string()),
                    "Abs" => MathLang::Abs(Box::new(MathLang::from(l[1].clone()))),
                    "Neg" => MathLang::Neg(Box::new(MathLang::from(l[1].clone()))),
                    "Add" => MathLang::Add(
                        Box::new(MathLang::from(l[1].clone())),
                        Box::new(MathLang::from(l[2].clone())),
                    ),
                    "Sub" => MathLang::Sub(
                        Box::new(MathLang::from(l[1].clone())),
                        Box::new(MathLang::from(l[2].clone())),
                    ),
                    "Mul" => MathLang::Mul(
                        Box::new(MathLang::from(l[1].clone())),
                        Box::new(MathLang::from(l[2].clone())),
                    ),
                    "Div" => MathLang::Div(
                        Box::new(MathLang::from(l[1].clone())),
                        Box::new(MathLang::from(l[2].clone())),
                    ),
                    "Gt" => MathLang::Gt(
                        Box::new(MathLang::from(l[1].clone())),
                        Box::new(MathLang::from(l[2].clone())),
                    ),
                    "Neq" => MathLang::Neq(
                        Box::new(MathLang::from(l[1].clone())),
                        Box::new(MathLang::from(l[2].clone())),
                    ),
                    _ => unreachable!(),
                }
            }
            _ => unreachable!(),
        }
    }
}

impl ChompyLanguage for MathLang {
    type Constant = i64;
    fn get_name(&self) -> String {
        "MathLang".to_string()
    }

    fn get_vals(&self) -> Vec<Self::Constant> {
        vec![]
    }

    fn get_vars(&self) -> Vec<String> {
        vec!["x".to_string(), "y".to_string(), "z".to_string()]
    }

    fn const_type_as_str(&self) -> String {
        "i64".to_string()
    }

    fn validate_rule(&self, rule: &Rule) -> ValidationResult {
        let mut cfg = z3::Config::new();
        cfg.set_timeout_msec(1000);
        let ctx = z3::Context::new(&cfg);
        let solver = z3::Solver::new(&ctx);
        let lhs = mathlang_to_z3(&ctx, &MathLang::from(rule.lhs.clone()));
        let rhs = mathlang_to_z3(&ctx, &MathLang::from(rule.rhs.clone()));
        if rule.condition.is_some() {
            let cond = MathLang::from(rule.condition.clone().unwrap());
            let cond_expr = mathlang_to_z3(&ctx, &cond);
            let zero = z3::ast::Int::from_i64(&ctx, 0);
            let cond = z3::ast::Bool::not(&cond_expr._eq(&zero));
            solver.assert(&z3::ast::Bool::implies(&cond, &lhs._eq(&rhs)).not());
        } else {
            solver.assert(&lhs._eq(&rhs).not());
        }
        match solver.check() {
            z3::SatResult::Unsat => ValidationResult::Valid,
            z3::SatResult::Unknown => ValidationResult::Unknown,
            z3::SatResult::Sat => ValidationResult::Invalid,
        }
    }

    fn get_predicates(&self) -> Workload {
        // TODO: bit of a hacky way to get around including constants in productions.
        // once chompy scales a bit better, we should just have
        // `let atoms = self.base_atoms()`.
        let atoms: Vec<String> = self
            .get_vals()
            .into_iter()
            .map(|val| self.make_val(val))
            .into_iter()
            .chain(self.get_vars().iter().map(|var| self.make_var(&var)))
            .map(|atom| atom.to_string())
            .collect();

        Workload::new(&["(BINOP EXPR EXPR)"])
            .plug("BINOP", &Workload::new(&["Neq", "Gt"]))
            .plug("EXPR", &Workload::new(atoms))
    }

    fn concretize_rule(&self, rule: &Rule) -> Vec<(Sexp, Sexp)> {
        fn construct_sexp(sexp: &Sexp, env: &HashMap<String, Sexp>) -> Sexp {
            if is_var(sexp) {
                if let Sexp::List(l) = sexp {
                    let id = l[1].clone();
                    return env[&id.to_string()].clone();
                }
                panic!();
            }
            match sexp {
                Sexp::Atom(_) => sexp.clone(),
                Sexp::List(l) => {
                    let mut new_l: Vec<Sexp> = vec![];
                    for t in l {
                        new_l.push(construct_sexp(t, env));
                    }
                    Sexp::List(new_l)
                }
            }
        }

        // TODO: fix mii so that cond(lhs) holds, and that we don't just do the non-conditional
        // method of leaving variables inside.
        let num_concretized_rules = 10;
        let vars: HashSet<String> = self.get_vars().into_iter().collect();

        // caches that map variables to their corresponding values (all should be constants for
        // now).
        let mut env_caches: Vec<HashMap<String, Sexp>> = vec![];

        let mut concretized_rules: Vec<(Sexp, Sexp)> = vec![];
        let ctx = z3::Context::new(&z3::Config::new());
        if let Some(cond) = &rule.condition {
            // this is trickier. we need to assign values to the variables such that the condition
            // holds.
            let one = z3::ast::Int::from_i64(&ctx, 1);
            for _ in 0..num_concretized_rules {
                // assert(cond)
                let mut assertions: Vec<z3::ast::Bool> = vec![];
                assertions.push(mathlang_to_z3(&ctx, &MathLang::from(cond.clone()))._eq(&one));
                // push some dummy assertions just to get all variables in scope.
                for var in &vars {
                    let const_var = z3::ast::Int::new_const(&ctx, var.clone());
                    // this assertion will always hold; a model which disproves the assertion
                    // above will not break this assertion.
                    assertions.push(const_var._eq(&const_var));
                }
                // there should also be one mega assertion which makes sure we don't generate
                // the same model twice.
                for env in env_caches.iter() {
                    for (var, val) in env {
                        assertions.push(
                            z3::ast::Int::new_const(&ctx, var.clone())
                                ._eq(&mathlang_to_z3(&ctx, &MathLang::from(val.clone())))
                                .not(),
                        );
                    }
                }
                // now, send this to the solver.
                let mut cfg = z3::Config::new();
                cfg.set_timeout_msec(1000);
                let solver = z3::Solver::new(&ctx);
                info!("assertions: {:?}", assertions);
                for assertion in &assertions {
                    solver.assert(assertion);
                }
                if let z3::SatResult::Sat = solver.check() {
                    let model = solver.get_model().unwrap();
                    info!("model: {:?}", model.to_string());
                    let mut env: HashMap<String, Sexp> = HashMap::default();
                    for var in &vars {
                        let val = model
                            .eval(&z3::ast::Int::new_const(&ctx, var.clone()))
                            .unwrap()
                            .as_i64()
                            .unwrap();
                        env.insert(var.clone(), self.make_val(val));
                    }
                    env_caches.push(env.clone());
                    // TODO: this bottom part isn't right yet; it should replace the variables
                    // inside lhs, rhs with the constants in `env`.
                    concretized_rules.push((
                        construct_sexp(&rule.lhs, &env),
                        construct_sexp(&rule.rhs, &env),
                    ));
                } else {
                    break;
                }
            }
        } else {
            let mut rng: StdRng = rand::SeedableRng::seed_from_u64(0xf00d4b0bacafe);
            for _ in 0..num_concretized_rules {
                let mut env: HashMap<String, Sexp> = HashMap::default();
                for v in &vars {
                    let val = rng.gen_range(-10..10);
                    env.insert(v.clone(), self.make_val(val));
                }
                concretized_rules.push((
                    construct_sexp(&rule.lhs, &env),
                    construct_sexp(&rule.rhs, &env),
                ));
            }
        }
        concretized_rules
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
                "Neq".to_string(),
                "Gt".to_string(),
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
            MathLang::Gt(e1, e2) => Sexp::List(vec![
                Sexp::Atom("Gt".to_string()),
                e1.make_sexp(),
                e2.make_sexp(),
            ]),
            MathLang::Neq(e1, e2) => Sexp::List(vec![
                Sexp::Atom("Neq".to_string()),
                e1.make_sexp(),
                e2.make_sexp(),
            ]),
        }
    }

    fn const_to_bool(&self, val: Constant<Self>) -> bool {
        if val == 0 {
            false
        } else if val == 1 {
            true
        } else {
            panic!()
        }
    }

    // TODO: include CVEC_LEN here
    fn eval(&self, sexp: &Sexp, env: &HashMap<String, CVec<Self>>) -> CVec<Self> {
        let term = MathLang::from(sexp.clone());
        match term {
            MathLang::Const(c) => vec![Some(c)],
            MathLang::Var(v) => {
                if let Some(x) = env.get(&v) {
                    x.clone()
                } else {
                    vec![None]
                }
            }
            MathLang::Abs(e) => {
                let e: CVec<Self> = self.eval(&e.make_sexp(), env);
                e.into_iter()
                    .map(|x| if let Some(x) = x { Some(x.abs()) } else { None })
                    .collect()
            }
            MathLang::Neg(e) => {
                let e: CVec<Self> = self.eval(&e.make_sexp(), env);
                e.into_iter()
                    .map(|x| if let Some(x) = x { Some(x.neg()) } else { None })
                    .collect()
            }
            MathLang::Add(ref e1, ref e2)
            | MathLang::Sub(ref e1, ref e2)
            | MathLang::Mul(ref e1, ref e2)
            | MathLang::Div(ref e1, ref e2) => {
                let e1 = self.eval(&e1.make_sexp(), env);
                let e2 = self.eval(&e2.make_sexp(), env);
                let f = match term {
                    MathLang::Add(_, _) => i64::checked_add,
                    MathLang::Sub(_, _) => i64::checked_sub,
                    MathLang::Mul(_, _) => i64::checked_mul,
                    MathLang::Div(_, _) => i64::checked_div,
                    _ => unreachable!(),
                };
                e1.into_iter()
                    .zip(e2.into_iter())
                    .map(|(x, y)| {
                        if x.is_none() || y.is_none() {
                            return None;
                        }
                        let x = x.unwrap();
                        let y = y.unwrap();
                        f(x, y)
                    })
                    .collect()
            }
            // binary conditions
            MathLang::Gt(ref e1, ref e2) | MathLang::Neq(ref e1, ref e2) => {
                let e1 = self.eval(&e1.make_sexp(), env);
                let e2 = self.eval(&e2.make_sexp(), env);
                let f = match term {
                    MathLang::Neq(_, _) => i64::ne,
                    MathLang::Gt(_, _) => i64::gt,
                    _ => unreachable!(),
                };
                e1.into_iter()
                    .zip(e2.into_iter())
                    .map(|(x, y)| {
                        if x.is_none() || y.is_none() {
                            return None;
                        }
                        let x = x.unwrap();
                        let y = y.unwrap();
                        if f(&x, &y) {
                            Some(1)
                        } else {
                            Some(0)
                        }
                    })
                    .collect()
            }
        }
    }
}

/// Converts the given `MathLang` term to a `z3::ast::Int`. This function is useful for
/// validating rules in the `MathLang` language.
fn mathlang_to_z3<'a>(ctx: &'a z3::Context, math_lang: &MathLang) -> z3::ast::Int<'a> {
    let zero = z3::ast::Int::from_i64(ctx, 0);
    let one = z3::ast::Int::from_i64(ctx, 1);
    match math_lang {
        MathLang::Const(c) => z3::ast::Int::from_i64(ctx, *c),
        MathLang::Var(v) => z3::ast::Int::new_const(ctx, v.to_string()),
        MathLang::Abs(e) => {
            let result = mathlang_to_z3(ctx, e);
            z3::ast::Bool::ite(
                &z3::ast::Int::ge(&result, &z3::ast::Int::from_i64(ctx, 0)),
                &result,
                &result.unary_minus(),
            )
        }
        MathLang::Neg(e) => mathlang_to_z3(ctx, e).unary_minus(),
        MathLang::Add(e1, e2) => {
            z3::ast::Int::add(&ctx, &[&mathlang_to_z3(ctx, e1), &mathlang_to_z3(ctx, e2)])
        }
        MathLang::Sub(e1, e2) => {
            z3::ast::Int::sub(&ctx, &[&mathlang_to_z3(ctx, e1), &mathlang_to_z3(ctx, e2)])
        }
        MathLang::Mul(e1, e2) => {
            z3::ast::Int::mul(&ctx, &[&mathlang_to_z3(ctx, e1), &mathlang_to_z3(ctx, e2)])
        }
        MathLang::Div(e1, e2) => mathlang_to_z3(ctx, e1).div(&mathlang_to_z3(ctx, e2)),
        MathLang::Gt(e1, e2) => z3::ast::Bool::ite(
            &mathlang_to_z3(ctx, e1).gt(&mathlang_to_z3(ctx, e2)),
            &one,
            &zero,
        ),
        MathLang::Neq(e1, e2) => z3::ast::Bool::ite(
            &z3::ast::Int::_eq(&mathlang_to_z3(ctx, e1), &mathlang_to_z3(ctx, e2)),
            &zero,
            &one,
        ),
    }
}
