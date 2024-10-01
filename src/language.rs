use std::fmt::Display;

pub type CVec<L> = Vec<Option<<L as ChompyLang>::Constant>>;
/// Value type in the domain.
pub type Constant<L> = <L as ChompyLang>::Constant;

pub trait ChompyLang {
    type Constant: Clone;

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
}

#[derive(Debug, Clone, PartialEq)]
pub enum MathLang {
    Num(i64),
    Var(String),
    Add(Box<MathLang>, Box<MathLang>),
    Sub(Box<MathLang>, Box<MathLang>),
    Mul(Box<MathLang>, Box<MathLang>),
    Div(Box<MathLang>, Box<MathLang>),
}

impl ChompyLang for MathLang {
    type Constant = i64;

    fn parse(statement: &str) -> Self {
        assert!(statement.starts_with("(") && statement.ends_with(")"));
        // get the first token
        let mut tokens = statement[1..statement.len() - 1].split_whitespace();
        let operator = tokens.next().unwrap();
        let children = MathLang::_get_children(statement);
        match operator {
            "Num" => MathLang::Num(children[0].parse().unwrap()),
            "Var" => MathLang::Var(children[0].clone()),
            _ => {
                let left = Box::new(MathLang::parse(&children[0]));
                let right = Box::new(MathLang::parse(&children[1]));
                match operator {
                    "Add" => MathLang::Add(left, right),
                    "Sub" => MathLang::Sub(left, right),
                    "Mul" => MathLang::Mul(left, right),
                    "Div" => MathLang::Div(left, right),
                    _ => panic!("Unknown operator: {}", operator),
                }
            }
        }
    }

    fn to_sexpr(&self) -> String {
        match self {
            MathLang::Num(n) => format!("(Num {})", n),
            MathLang::Var(v) => format!("(Var \"{}\")", v),
            MathLang::Add(l, r) => format!("(Add {} {})", l.to_sexpr(), r.to_sexpr()),
            MathLang::Sub(l, r) => format!("(Sub {} {})", l.to_sexpr(), r.to_sexpr()),
            MathLang::Mul(l, r) => format!("(Mul {} {})", l.to_sexpr(), r.to_sexpr()),
            MathLang::Div(l, r) => format!("(Div {} {})", l.to_sexpr(), r.to_sexpr()),
        }
    }
}

impl Display for MathLang {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_sexpr())
    }
}
