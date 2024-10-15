use egglog::EGraph;
use ruler::enumo;

#[ignore]
#[test]
fn math_eval() {
    let mut egraph = EGraph::default();
    egraph
        .parse_and_run_program(
            Some("egglog/math.egg".to_string()),
            include_str!("egglog/math-old.egg"),
        )
        .unwrap();

    // begin by enumerating the language

    let unary_fns = enumo::Workload::new(&["(Abs)"]);
    let binary_fns = enumo::Workload::new(&["(Add)", "(Sub)", "(Mul)", "(Div)"]);

    let pred_binary_fns = enumo::Workload::new(&["(Eq)", "(Neq)"]);

    let atoms = enumo::Workload::new(&["(Num 0)", "(Num 1)", "(Var quoteaquote)"]);

    let term_productions = enumo::Workload::new(&["(MathOp2 mathop x y)", "(PredOp2 predop x y)"])
        .plug("mathop", &binary_fns)
        .plug("predop", &pred_binary_fns);

    let terms_depth_1 = term_productions.plug("x", &atoms).plug("y", &atoms);

    let mut prog: String = String::new();
    for term in terms_depth_1.force() {
        let term_str = term.to_string().replace("quote", "\"");
        prog = format!("{}\n{}", prog, term_str);
    }
    prog += "\n(run 20)\n";

    let extracts = egraph.parse_and_run_program(None, &prog).unwrap();
    for extract in extracts {
        println!("{}", extract);
    }
    let serialized = egraph.serialize(egglog::SerializeConfig::default());
    serialized.to_json_file("math.svg").unwrap();
}
