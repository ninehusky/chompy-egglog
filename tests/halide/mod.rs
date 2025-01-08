use chompy::{
    chomper::Rule,
    language::{CVec, ChompyLanguage, ValidationResult},
    PredicateInterpreter,
};

use log::info;

use rand::Rng;
use rand::{rngs::StdRng, SeedableRng};

use ruler::{
    enumo::{Sexp, Workload},
    HashMap, HashSet,
};
use z3::ast::Ast;

/// Definition of the Halide language and Chomper.

pub enum HalideLanguage {
    Const(i64),
    Lt(Box<HalideLanguage>, Box<HalideLanguage>),
    Leq(Box<HalideLanguage>, Box<HalideLanguage>),
    Eq(Box<HalideLanguage>, Box<HalideLanguage>),
    Neq(Box<HalideLanguage>, Box<HalideLanguage>),
    Implies(Box<HalideLanguage>, Box<HalideLanguage>),
    Not(Box<HalideLanguage>),
    Neg(Box<HalideLanguage>),
    And(Box<HalideLanguage>, Box<HalideLanguage>),
    Or(Box<HalideLanguage>, Box<HalideLanguage>),
    Xor(Box<HalideLanguage>, Box<HalideLanguage>),
    Add(Box<HalideLanguage>, Box<HalideLanguage>),
    Sub(Box<HalideLanguage>, Box<HalideLanguage>),
    Mul(Box<HalideLanguage>, Box<HalideLanguage>),
    Div(Box<HalideLanguage>, Box<HalideLanguage>),
    Min(Box<HalideLanguage>, Box<HalideLanguage>),
    Max(Box<HalideLanguage>, Box<HalideLanguage>),
    Select(
        Box<HalideLanguage>,
        Box<HalideLanguage>,
        Box<HalideLanguage>,
    ),
    Var(String),
}

impl From<Sexp> for HalideLanguage {
    fn from(sexp: Sexp) -> Self {
        match sexp {
            Sexp::List(l) => {
                let op = l[0].clone();
                match op.to_string().as_str() {
                    "Const" => HalideLanguage::Const(l[1].to_string().parse().unwrap()),
                    "Lt" => HalideLanguage::Lt(
                        Box::new(HalideLanguage::from(l[1].clone())),
                        Box::new(HalideLanguage::from(l[2].clone())),
                    ),
                    "Leq" => HalideLanguage::Leq(
                        Box::new(HalideLanguage::from(l[1].clone())),
                        Box::new(HalideLanguage::from(l[2].clone())),
                    ),
                    "Eq" => HalideLanguage::Eq(
                        Box::new(HalideLanguage::from(l[1].clone())),
                        Box::new(HalideLanguage::from(l[2].clone())),
                    ),
                    "Neq" => HalideLanguage::Neq(
                        Box::new(HalideLanguage::from(l[1].clone())),
                        Box::new(HalideLanguage::from(l[2].clone())),
                    ),
                    "Implies" => HalideLanguage::Implies(
                        Box::new(HalideLanguage::from(l[1].clone())),
                        Box::new(HalideLanguage::from(l[2].clone())),
                    ),
                    "Not" => HalideLanguage::Not(Box::new(HalideLanguage::from(l[1].clone()))),
                    "Neg" => HalideLanguage::Neg(Box::new(HalideLanguage::from(l[1].clone()))),
                    "And" => HalideLanguage::And(
                        Box::new(HalideLanguage::from(l[1].clone())),
                        Box::new(HalideLanguage::from(l[2].clone())),
                    ),
                    "Or" => HalideLanguage::Or(
                        Box::new(HalideLanguage::from(l[1].clone())),
                        Box::new(HalideLanguage::from(l[2].clone())),
                    ),
                    "Xor" => HalideLanguage::Xor(
                        Box::new(HalideLanguage::from(l[1].clone())),
                        Box::new(HalideLanguage::from(l[2].clone())),
                    ),
                    "Add" => HalideLanguage::Add(
                        Box::new(HalideLanguage::from(l[1].clone())),
                        Box::new(HalideLanguage::from(l[2].clone())),
                    ),
                    "Sub" => HalideLanguage::Sub(
                        Box::new(HalideLanguage::from(l[1].clone())),
                        Box::new(HalideLanguage::from(l[2].clone())),
                    ),
                    "Mul" => HalideLanguage::Mul(
                        Box::new(HalideLanguage::from(l[1].clone())),
                        Box::new(HalideLanguage::from(l[2].clone())),
                    ),
                    "Div" => HalideLanguage::Div(
                        Box::new(HalideLanguage::from(l[1].clone())),
                        Box::new(HalideLanguage::from(l[2].clone())),
                    ),
                    "Min" => HalideLanguage::Min(
                        Box::new(HalideLanguage::from(l[1].clone())),
                        Box::new(HalideLanguage::from(l[2].clone())),
                    ),
                    "Max" => HalideLanguage::Max(
                        Box::new(HalideLanguage::from(l[1].clone())),
                        Box::new(HalideLanguage::from(l[2].clone())),
                    ),
                    "Select" => HalideLanguage::Select(
                        Box::new(HalideLanguage::from(l[1].clone())),
                        Box::new(HalideLanguage::from(l[2].clone())),
                        Box::new(HalideLanguage::from(l[3].clone())),
                    ),
                    "Var" => HalideLanguage::Var(l[1].to_string()),
                    _ => panic!("Invalid HalideLanguage op: {}", op),
                }
            }
            _ => unreachable!(),
        }
    }
}

impl HalideLanguage {
    fn get_cvec_len(&self) -> usize {
        20
    }

    fn to_z3<'a>(&self, ctx: &'a z3::Context) -> z3::ast::Int<'a> {
        let one = z3::ast::Int::from_i64(&ctx, 1);
        let zero = z3::ast::Int::from_i64(&ctx, 0);
        match self {
            HalideLanguage::Var(v) => z3::ast::Int::new_const(ctx, v.to_string()),
            HalideLanguage::Const(val) => z3::ast::Int::from_i64(&ctx, *val),
            HalideLanguage::Lt(lhs, rhs) => z3::ast::Bool::ite(
                &z3::ast::Int::lt(&lhs.to_z3(ctx), &rhs.to_z3(ctx)),
                &one,
                &zero,
            ),
            HalideLanguage::Leq(lhs, rhs) => z3::ast::Bool::ite(
                &z3::ast::Int::le(&lhs.to_z3(ctx), &rhs.to_z3(ctx)),
                &one,
                &zero,
            ),
            HalideLanguage::Eq(lhs, rhs) => {
                z3::ast::Bool::ite(&lhs.to_z3(ctx)._eq(&rhs.to_z3(ctx)), &one, &zero)
            }
            HalideLanguage::Neq(lhs, rhs) => {
                z3::ast::Bool::ite(&lhs.to_z3(ctx)._eq(&rhs.to_z3(ctx)).not(), &one, &zero)
            }
            HalideLanguage::Implies(lhs, rhs) => {
                let l_not_z = lhs.to_z3(ctx)._eq(&zero).not();
                let r_not_z = rhs.to_z3(ctx)._eq(&zero).not();
                z3::ast::Bool::ite(&z3::ast::Bool::implies(&l_not_z, &r_not_z), &one, &zero)
            }
            HalideLanguage::Not(expr) => {
                z3::ast::Bool::ite(&expr.to_z3(ctx)._eq(&zero), &one, &zero)
            }
            HalideLanguage::Neg(expr) => z3::ast::Int::unary_minus(&expr.to_z3(ctx)),
            HalideLanguage::And(lhs, rhs) => {
                let l_bool = lhs.to_z3(ctx)._eq(&zero).not();
                let r_bool = rhs.to_z3(ctx)._eq(&zero).not();
                z3::ast::Bool::ite(&z3::ast::Bool::and(ctx, &[&l_bool, &r_bool]), &one, &zero)
            }
            HalideLanguage::Or(lhs, rhs) => {
                let l_bool = lhs.to_z3(ctx)._eq(&zero).not();
                let r_bool = rhs.to_z3(ctx)._eq(&zero).not();
                z3::ast::Bool::ite(&z3::ast::Bool::or(ctx, &[&l_bool, &r_bool]), &one, &zero)
            }
            HalideLanguage::Xor(lhs, rhs) => {
                let l_bool = lhs.to_z3(ctx)._eq(&zero).not();
                let r_bool = rhs.to_z3(ctx)._eq(&zero).not();
                z3::ast::Bool::ite(&z3::ast::Bool::xor(&l_bool, &r_bool), &one, &zero)
            }
            HalideLanguage::Add(lhs, rhs) => {
                z3::ast::Int::add(&ctx, &[&lhs.to_z3(ctx), &rhs.to_z3(ctx)])
            }
            HalideLanguage::Sub(lhs, rhs) => {
                z3::ast::Int::sub(&ctx, &[&lhs.to_z3(ctx), &rhs.to_z3(ctx)])
            }
            HalideLanguage::Mul(lhs, rhs) => {
                z3::ast::Int::mul(&ctx, &[&lhs.to_z3(ctx), &rhs.to_z3(ctx)])
            }
            HalideLanguage::Div(lhs, rhs) => z3::ast::Bool::ite(
                &rhs.to_z3(ctx)._eq(&zero),
                &zero,
                &z3::ast::Int::div(&lhs.to_z3(ctx), &rhs.to_z3(ctx)),
            ),
            HalideLanguage::Min(lhs, rhs) => z3::ast::Bool::ite(
                &z3::ast::Int::lt(&lhs.to_z3(ctx), &rhs.to_z3(ctx)),
                &lhs.to_z3(ctx),
                &rhs.to_z3(ctx),
            ),
            HalideLanguage::Max(lhs, rhs) => z3::ast::Bool::ite(
                &z3::ast::Int::lt(&lhs.to_z3(ctx), &rhs.to_z3(ctx)),
                &rhs.to_z3(ctx),
                &lhs.to_z3(ctx),
            ),
            HalideLanguage::Select(cond, lhs, rhs) => z3::ast::Bool::ite(
                &cond.to_z3(ctx)._eq(&zero),
                &rhs.to_z3(ctx),
                &lhs.to_z3(ctx),
            ),
        }
    }
}

impl ChompyLanguage for HalideLanguage {
    type Constant = i64;

    fn get_name(&self) -> String {
        "HalideLanguage".into()
    }

    fn get_vars(&self) -> Vec<String> {
        vec!["x".into(), "y".into(), "z".into()]
    }

    fn get_vals(&self) -> Vec<Self::Constant> {
        vec![-1, 0, 1]
    }

    fn get_predicates(&self) -> ruler::enumo::Workload {
        // TODO: bit of a hacky way to get around including constants in productions.
        let atoms: Vec<String> = self
            .get_vals()
            .into_iter()
            .map(|val| self.make_val(val))
            .into_iter()
            .chain(self.get_vars().iter().map(|var| self.make_var(&var)))
            .map(|atom| atom.to_string())
            .collect();

        Workload::new(&["(BINOP EXPR EXPR)"])
            .plug(
                "BINOP",
                &Workload::new(&["Lt", "Leq", "Eq", "Neq", "Implies"]),
            )
            .plug("EXPR", &Workload::new(atoms))
    }

    fn make_val(&self, val: chompy::language::Constant<Self>) -> Sexp {
        Sexp::List(vec![
            Sexp::Atom("Const".into()),
            Sexp::Atom(val.to_string()),
        ])
    }

    fn const_to_bool(&self, val: chompy::language::Constant<Self>) -> bool {
        val != 0
    }

    fn make_var(&self, var: &str) -> Sexp {
        Sexp::List(vec![Sexp::Atom("Var".into()), Sexp::Atom(var.into())])
    }

    fn get_funcs(&self) -> Vec<Vec<String>> {
        vec![
            vec![],
            vec!["Not".into(), "Neg".into()],
            vec![
                "Lt".into(),
                "Leq".into(),
                "Eq".into(),
                "Neq".into(),
                "Implies".into(),
                "And".into(),
                "Or".into(),
                "Xor".into(),
                "Add".into(),
                "Sub".into(),
                "Mul".into(),
                "Div".into(),
                "Min".into(),
                "Max".into(),
            ],
            vec!["Select".into()],
        ]
    }

    fn validate_rule(&self, rule: &chompy::chomper::Rule) -> chompy::language::ValidationResult {
        let mut cfg = z3::Config::new();
        cfg.set_timeout_msec(1000);
        let ctx = z3::Context::new(&cfg);
        let solver = z3::Solver::new(&ctx);
        let lhs = HalideLanguage::from(rule.lhs.clone()).to_z3(&ctx);
        let rhs = HalideLanguage::from(rule.rhs.clone()).to_z3(&ctx);
        if let Some(cond) = rule.condition.clone() {
            let cond_expr = HalideLanguage::from(cond).to_z3(&ctx);
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

    fn concretize_rule(&self, rule: &Rule) -> Vec<(Sexp, Sexp)> {
        fn construct_sexp(sexp: &Sexp, env: &HashMap<String, Sexp>) -> Sexp {
            if chompy::language::is_var(sexp) {
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
                assertions.push(HalideLanguage::from(cond.clone()).to_z3(&ctx)._eq(&one));
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
                                ._eq(&HalideLanguage::from(val.clone()).to_z3(&ctx))
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

    fn const_type_as_str(&self) -> String {
        "i64".into()
    }

    fn eval(
        &self,
        sexp: &Sexp,
        env: &ruler::HashMap<String, chompy::language::CVec<Self>>,
    ) -> chompy::language::CVec<Self> {
        let term: HalideLanguage = HalideLanguage::from(sexp.clone());
        let cvec_len = self.get_cvec_len();
        let cvec = match term {
            HalideLanguage::Const(val) => vec![Some(val); cvec_len],
            HalideLanguage::Lt(lhs, rhs) => {
                let lhs = self.eval(&lhs.make_sexp(), env);
                let rhs = self.eval(&rhs.make_sexp(), env);
                lhs.iter()
                    .zip(rhs.iter())
                    .map(|(l, r)| Some(if l < r { 1 } else { 0 }))
                    .collect()
            }
            HalideLanguage::Leq(lhs, rhs) => {
                let lhs = self.eval(&lhs.make_sexp(), env);
                let rhs = self.eval(&rhs.make_sexp(), env);
                lhs.iter()
                    .zip(rhs.iter())
                    .map(|(l, r)| Some(if l <= r { 1 } else { 0 }))
                    .collect()
            }
            HalideLanguage::Eq(lhs, rhs) => {
                let lhs = self.eval(&lhs.make_sexp(), env);
                let rhs = self.eval(&rhs.make_sexp(), env);
                lhs.iter()
                    .zip(rhs.iter())
                    .map(|(l, r)| Some(if l == r { 1 } else { 0 }))
                    .collect()
            }
            HalideLanguage::Neq(lhs, rhs) => {
                let lhs = self.eval(&lhs.make_sexp(), env);
                let rhs = self.eval(&rhs.make_sexp(), env);
                lhs.iter()
                    .zip(rhs.iter())
                    .map(|(l, r)| Some(if l == r { 0 } else { 1 }))
                    .collect()
            }
            HalideLanguage::Implies(lhs, rhs) => {
                let lhs = self.eval(&lhs.make_sexp(), env);
                let rhs = self.eval(&rhs.make_sexp(), env);
                lhs.iter()
                    .zip(rhs.iter())
                    // \not p \vee q
                    .map(|(l, r)| {
                        if l.is_none() || r.is_none() {
                            return None;
                        }
                        Some(if l.unwrap() == 0 || r.unwrap() == 1 {
                            1
                        } else {
                            0
                        })
                    })
                    .collect()
            }
            HalideLanguage::Not(expr) => {
                let expr = self.eval(&expr.make_sexp(), env);
                expr.iter()
                    .map(|e| {
                        if e.is_none() {
                            return None;
                        }
                        Some(if e.unwrap() == 0 { 1 } else { 0 })
                    })
                    .collect()
            }
            HalideLanguage::Neg(expr) => {
                let expr = self.eval(&expr.make_sexp(), env);
                expr.iter()
                    .map(|e| {
                        if e.is_none() {
                            return None;
                        }
                        Some(-e.unwrap())
                    })
                    .collect()
            }
            HalideLanguage::And(lhs, rhs) => {
                let lhs = self.eval(&lhs.make_sexp(), env);
                let rhs = self.eval(&rhs.make_sexp(), env);
                lhs.iter()
                    .zip(rhs.iter())
                    .map(|(l, r)| {
                        if l.is_none() || r.is_none() {
                            return None;
                        }
                        Some(if l.unwrap() >= 0 && r.unwrap() >= 0 {
                            1
                        } else {
                            0
                        })
                    })
                    .collect()
            }
            HalideLanguage::Or(lhs, rhs) => {
                let lhs = self.eval(&lhs.make_sexp(), env);
                let rhs = self.eval(&rhs.make_sexp(), env);
                lhs.iter()
                    .zip(rhs.iter())
                    .map(|(l, r)| {
                        if l.is_none() || r.is_none() {
                            return None;
                        }
                        Some(if l.unwrap() >= 0 || r.unwrap() >= 0 {
                            1
                        } else {
                            0
                        })
                    })
                    .collect()
            }
            HalideLanguage::Xor(lhs, rhs) => {
                let lhs = self.eval(&lhs.make_sexp(), env);
                let rhs = self.eval(&rhs.make_sexp(), env);
                lhs.iter()
                    .zip(rhs.iter())
                    .map(|(l, r)| {
                        if l.is_none() || r.is_none() {
                            return None;
                        }
                        Some(if (l.unwrap() != 0) ^ (r.unwrap() != 0) {
                            1
                        } else {
                            0
                        })
                    })
                    .collect()
            }
            HalideLanguage::Add(lhs, rhs) => {
                let lhs = self.eval(&lhs.make_sexp(), env);
                let rhs = self.eval(&rhs.make_sexp(), env);
                lhs.iter()
                    .zip(rhs.iter())
                    .map(|(l, r)| {
                        if l.is_none() || r.is_none() {
                            return None;
                        } else {
                            i64::checked_add(l.unwrap(), r.unwrap())
                        }
                    })
                    .collect()
            }
            HalideLanguage::Sub(lhs, rhs) => {
                let lhs = self.eval(&lhs.make_sexp(), env);
                let rhs = self.eval(&rhs.make_sexp(), env);
                lhs.iter()
                    .zip(rhs.iter())
                    .map(|(l, r)| {
                        if l.is_none() || r.is_none() {
                            return None;
                        } else {
                            i64::checked_sub(l.unwrap(), r.unwrap())
                        }
                    })
                    .collect()
            }
            HalideLanguage::Mul(lhs, rhs) => {
                let lhs = self.eval(&lhs.make_sexp(), env);
                let rhs = self.eval(&rhs.make_sexp(), env);
                lhs.iter()
                    .zip(rhs.iter())
                    .map(|(l, r)| {
                        if l.is_none() || r.is_none() {
                            return None;
                        } else {
                            i64::checked_mul(l.unwrap(), r.unwrap())
                        }
                    })
                    .collect()
            }
            HalideLanguage::Div(lhs, rhs) => {
                let lhs = self.eval(&lhs.make_sexp(), env);
                let rhs = self.eval(&rhs.make_sexp(), env);
                lhs.iter()
                    .zip(rhs.iter())
                    .map(|(l, r)| {
                        if l.is_none() || r.is_none() {
                            return None;
                        } else {
                            if r.unwrap() == 0 {
                                Some(0)
                            } else {
                                Some(l.unwrap() / r.unwrap())
                            }
                        }
                    })
                    .collect()
            }
            HalideLanguage::Min(lhs, rhs) => {
                let lhs = self.eval(&lhs.make_sexp(), env);
                let rhs = self.eval(&rhs.make_sexp(), env);
                lhs.iter()
                    .zip(rhs.iter())
                    .map(|(l, r)| {
                        if l.is_none() || r.is_none() {
                            return None;
                        }
                        Some(i64::min(l.unwrap(), r.unwrap()))
                    })
                    .collect()
            }
            HalideLanguage::Max(lhs, rhs) => {
                let lhs = self.eval(&lhs.make_sexp(), env);
                let rhs = self.eval(&rhs.make_sexp(), env);
                lhs.iter()
                    .zip(rhs.iter())
                    .map(|(l, r)| {
                        if l.is_none() || r.is_none() {
                            return None;
                        }
                        Some(i64::max(l.unwrap(), r.unwrap()))
                    })
                    .collect()
            }
            HalideLanguage::Select(cond, lhs, rhs) => {
                let cond = self.eval(&cond.make_sexp(), env);
                let lhs = self.eval(&lhs.make_sexp(), env);
                let rhs = self.eval(&rhs.make_sexp(), env);
                cond.iter()
                    .zip(lhs.iter().zip(rhs.iter()))
                    .map(|(c, (l, r))| if c.unwrap() != 0 { *l } else { *r })
                    .collect()
            }
            HalideLanguage::Var(var) => {
                if let Some(cvec) = env.get(&var) {
                    cvec.clone()
                } else {
                    vec![None; cvec_len]
                }
            }
        };
        assert_eq!(cvec.len(), cvec_len);
        cvec
    }

    fn make_sexp(&self) -> Sexp {
        match self {
            HalideLanguage::Const(val) => Sexp::List(vec![
                Sexp::Atom("Const".into()),
                Sexp::Atom(val.to_string()),
            ]),
            HalideLanguage::Lt(lhs, rhs) => Sexp::List(vec![
                Sexp::Atom("Lt".into()),
                lhs.make_sexp(),
                rhs.make_sexp(),
            ]),
            HalideLanguage::Leq(lhs, rhs) => Sexp::List(vec![
                Sexp::Atom("Leq".into()),
                lhs.make_sexp(),
                rhs.make_sexp(),
            ]),
            HalideLanguage::Eq(lhs, rhs) => Sexp::List(vec![
                Sexp::Atom("Eq".into()),
                lhs.make_sexp(),
                rhs.make_sexp(),
            ]),
            HalideLanguage::Neq(lhs, rhs) => Sexp::List(vec![
                Sexp::Atom("Neq".into()),
                lhs.make_sexp(),
                rhs.make_sexp(),
            ]),
            HalideLanguage::Implies(lhs, rhs) => Sexp::List(vec![
                Sexp::Atom("Implies".into()),
                lhs.make_sexp(),
                rhs.make_sexp(),
            ]),
            HalideLanguage::Not(expr) => {
                Sexp::List(vec![Sexp::Atom("Not".into()), expr.make_sexp()])
            }
            HalideLanguage::Neg(expr) => {
                Sexp::List(vec![Sexp::Atom("Neg".into()), expr.make_sexp()])
            }
            HalideLanguage::And(lhs, rhs) => Sexp::List(vec![
                Sexp::Atom("And".into()),
                lhs.make_sexp(),
                rhs.make_sexp(),
            ]),
            HalideLanguage::Or(lhs, rhs) => Sexp::List(vec![
                Sexp::Atom("Or".into()),
                lhs.make_sexp(),
                rhs.make_sexp(),
            ]),
            HalideLanguage::Xor(lhs, rhs) => Sexp::List(vec![
                Sexp::Atom("Xor".into()),
                lhs.make_sexp(),
                rhs.make_sexp(),
            ]),
            HalideLanguage::Add(lhs, rhs) => Sexp::List(vec![
                Sexp::Atom("Add".into()),
                lhs.make_sexp(),
                rhs.make_sexp(),
            ]),
            HalideLanguage::Sub(lhs, rhs) => Sexp::List(vec![
                Sexp::Atom("Sub".into()),
                lhs.make_sexp(),
                rhs.make_sexp(),
            ]),
            HalideLanguage::Mul(lhs, rhs) => Sexp::List(vec![
                Sexp::Atom("Mul".into()),
                lhs.make_sexp(),
                rhs.make_sexp(),
            ]),
            HalideLanguage::Div(lhs, rhs) => Sexp::List(vec![
                Sexp::Atom("Div".into()),
                lhs.make_sexp(),
                rhs.make_sexp(),
            ]),
            HalideLanguage::Min(lhs, rhs) => Sexp::List(vec![
                Sexp::Atom("Min".into()),
                lhs.make_sexp(),
                rhs.make_sexp(),
            ]),
            HalideLanguage::Max(lhs, rhs) => Sexp::List(vec![
                Sexp::Atom("Max".into()),
                lhs.make_sexp(),
                rhs.make_sexp(),
            ]),
            HalideLanguage::Select(cond, lhs, rhs) => Sexp::List(vec![
                Sexp::Atom("Select".into()),
                cond.make_sexp(),
                lhs.make_sexp(),
                rhs.make_sexp(),
            ]),
            HalideLanguage::Var(var) => {
                Sexp::List(vec![Sexp::Atom("Var".into()), Sexp::Atom(var.into())])
            }
        }
    }
}

pub struct HalideChomper;

impl chompy::chomper::Chomper for HalideChomper {
    type Constant = i64;

    fn make_pred_interpreter() -> impl PredicateInterpreter {
        #[derive(Debug)]
        struct DummyPredicateInterpreter;
        impl PredicateInterpreter for DummyPredicateInterpreter {
            fn interp_cond(&self, sexp: &ruler::enumo::Sexp) -> bool {
                let dummy_term = HalideLanguage::Var("dummy".to_string());
                match dummy_term.eval(sexp, &Default::default()).get(0).unwrap() {
                    Some(val) => *val > 0,
                    None => false,
                }
            }
        }
        DummyPredicateInterpreter
    }

    fn initialize_env(
        &self,
    ) -> ruler::HashMap<String, CVec<dyn ChompyLanguage<Constant = Self::Constant>>> {
        let mut env = ruler::HashMap::default();
        let seed = 0xf00d4b0bacafe;
        let cvec_len = 20;
        let mut rng = StdRng::seed_from_u64(seed);

        for var in self.get_language().get_vars() {
            let cvec = (0..cvec_len)
                .map(|_| Some(rng.gen_range(-10..10)))
                .collect::<CVec<HalideLanguage>>();
            env.insert(var.clone(), cvec);
        }
        env
    }

    fn get_language(&self) -> Box<impl ChompyLanguage<Constant = Self::Constant>> {
        Box::new(HalideLanguage::Var("dummy".to_string()))
    }
}

pub mod tests {
    use crate::halide::HalideChomper;
    use chompy::chomper::Chomper;

    #[test]
    fn run() {
        let chomper = HalideChomper;
        chomper.run_chompy(10);
    }
}
