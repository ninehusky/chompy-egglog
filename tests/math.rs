use chompy::language::*;

#[test]
fn test() {
    let prog = MathLang::parse("(Add (Var x) (Mul (Num 234) (Num 239487)))");
    println!("{:?}", prog);
}
