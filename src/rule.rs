use egglog::ast::{Action, Expr};

pub struct Rule {
    name: String,
    condition: Option<Expr>,
    lhs: Expr,
    rhs: Expr,
}

// impl Rule {
//     fn make_rule(rule: Rule) -> Action {
//         match rule.condition {
//             Some(_) => todo!(),
//             None => {
//                 let rw_command = format!("(rewrite {} {})", rule.lhs.to_sexp(), rule.rhs.to_sexp());
//                 egglog::ast::parse::ActionParser::new()
//                     .parse(&rw_command)
//                     .unwrap()
//             }
//         }
//     }
// }
