use crate::Workload;

pub fn intel_rules() -> Workload {
    let binary_ops = vec!["(Add)", "(Sub)", "(Mul)", "(Shl)", "(Shr)"];
    // commutativity
    let binary_commutativity = Workload::new(&[
        "(BVOp2 (ValueVar p) binop (Bitvector (ValueVar q) (ValueVar a)) (Bitvector (ValueVar r) (ValueVar b)))",
        "(BVOp2 (ValueVar p) binop (Bitvector (ValueVar r) (ValueVar b)) (Bitvector (ValueVar p) (ValueVar a)))",
    ])
    .plug("binop", &Workload::new(binary_ops));

    Workload::empty().append(binary_commutativity)
}
