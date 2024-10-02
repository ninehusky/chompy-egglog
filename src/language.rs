use std::fmt::Display;

pub type CVec<L> = Vec<Option<<L as ChompyLang>::Constant>>;
/// Value type in the domain.
pub type Constant<L> = <L as ChompyLang>::Constant;

pub trait ChompyLang {
    type Constant: Clone + Display;

    // returns the expression for the given statement.
    fn parse(statement: &str) -> Self;

    fn to_sexpr(&self) -> String;

    fn _get_children(statement: &str) -> Vec<String> {
        let mut depth = 0;
        let mut args: Vec<String> = vec![];
        let mut current_arg = String::new();
        // split the token on whitespace, removing the first one.
        let tokens = statement[1..statement.len() - 1]
            .split_whitespace()
            .skip(1)
            .collect::<Vec<&str>>();
        for token in tokens {
            if token.starts_with("(") {
                depth += 1;
            }
            if token.ends_with(")") {
                depth -= 1;
            }

            if !current_arg.is_empty() {
                current_arg.push_str(" ");
            }
            current_arg.push_str(token);
            if depth == 0 {
                args.push(current_arg.clone());
                current_arg.clear();
            }
        }
        if !current_arg.is_empty() {
            args.push(current_arg);
        }
        args
    }

    fn cvec_to_sexpr(cvec: &CVec<Self>) -> String {
        let elements = cvec
            .iter()
            .map(|x| match x {
                Some(x) => format!("(Some {})", x),
                None => "(None)".to_string(),
            })
            .collect::<Vec<String>>();
        // then, join them with a space.
        let together = format!("{}", elements.join(" "));
        format!("(vec-of {})", together)
    }
}
