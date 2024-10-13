use egglog::EGraph;

#[test]
fn math_eval() {
    let mut egraph = EGraph::default();
    egraph
        .parse_and_run_program(
            Some("egglog/math.egg".to_string()),
            include_str!("egglog/math-old.egg"),
        )
        .unwrap();
    let serialized = egraph.serialize(egglog::SerializeConfig::default());
    serialized.to_json_file("math.svg").unwrap();
}
