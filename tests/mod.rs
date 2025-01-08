pub mod halide;

pub mod tests {
    use chompy::ite::PredicateInterpreter;
    use chompy::language::MathLang;

    use chompy::chomper::Chomper;
    use chompy::language::*;

    use rand::rngs::StdRng;
    use rand::{Rng, SeedableRng};

    #[test]
    fn test_chomper() {
        struct MathChomper;

        impl Chomper for MathChomper {
            type Constant = i64;

            fn make_pred_interpreter() -> impl chompy::ite::PredicateInterpreter {
                #[derive(Debug)]
                struct DummyPredicateInterpreter;
                impl PredicateInterpreter for DummyPredicateInterpreter {
                    fn interp_cond(&self, sexp: &ruler::enumo::Sexp) -> bool {
                        let dummy_term = MathLang::Var("dummy".to_string());
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
            ) -> ruler::HashMap<String, CVec<dyn ChompyLanguage<Constant = Self::Constant>>>
            {
                let mut env = ruler::HashMap::default();
                // make seedable rng
                let seed = 0b1001;
                // TODO: this should be part of the interface for eval?
                let cvec_len = 10;
                let mut rng = StdRng::seed_from_u64(seed);

                for var in self.get_language().get_vars() {
                    let cvec = (0..cvec_len)
                        .map(|_| Some(rng.gen_range(-10..10)))
                        .collect::<CVec<MathLang>>();
                    env.insert(var.clone(), cvec);
                }
                env
            }

            fn get_language(&self) -> Box<impl ChompyLanguage<Constant = Self::Constant>> {
                Box::new(MathLang::Var("dummy".to_string()))
            }
        }

        let chomper = MathChomper;
        let rules = chomper.run_chompy(10);
        for rule in rules {
            println!("{}", rule);
        }
    }
}
