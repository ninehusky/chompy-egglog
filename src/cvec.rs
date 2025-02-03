use std::sync::{Arc, Mutex};

use std::str::FromStr;

use ruler::enumo::Sexp;

use egglog::{
    ast::{Span, Symbol},
    constraint::SimpleTypeConstraint,
    sort::{FromSort, Sort, StringSort},
    util::IndexMap,
    EGraph, PrimitiveLike, Value,
};

const NONE_CVEC_IDENTIFIER: &str = "NoneCvec";

type CvecMap = IndexMap<Value, String>;

/// Wow, I can't believe we're back to creating this!
pub fn to_cvec_val(s: Symbol) -> Value {
    egglog::Value {
        // TODO: this is so weird.. commenting out the line below
        // makes this work when using `cargo flamegraph`?
        tag: "Cvec".into(),
        bits: Value::from(s).bits,
    }
}

#[derive(Debug)]
pub struct CvecSort {
    cvecs: Mutex<CvecMap>,
}

impl CvecSort {
    pub fn new() -> Self {
        let mut cvecs: CvecMap = Default::default();
        let val = to_cvec_val(NONE_CVEC_IDENTIFIER.into());
        cvecs.insert(val, NONE_CVEC_IDENTIFIER.to_string());
        let cvecs = Mutex::new(cvecs);
        Self { cvecs }
    }
}

impl Sort for CvecSort {
    fn name(&self) -> Symbol {
        "Cvec".into()
    }

    fn as_arc_any(
        self: std::sync::Arc<Self>,
    ) -> std::sync::Arc<dyn std::any::Any + Send + Sync + 'static> {
        self
    }

    fn extract_term(
        &self,
        _egraph: &egglog::EGraph,
        value: egglog::Value,
        _extractor: &egglog::extract::Extractor,
        termdag: &mut egglog::TermDag,
    ) -> Option<(egglog::extract::Cost, egglog::Term)> {
        let cvecs = self.cvecs.lock().unwrap();
        let val: String = cvecs.get(&value).unwrap().to_string();

        if val == NONE_CVEC_IDENTIFIER {
            Some((1, termdag.app(Symbol::from("NoneCvec"), vec![])))
        } else {
            let args = vec![termdag.lit(egglog::ast::Literal::String(Symbol::from(val)))];
            Some((1, termdag.app(Symbol::from("SomeCvec"), args)))
        }
    }

    fn register_primitives(self: std::sync::Arc<Self>, info: &mut egglog::TypeInfo) {
        info.add_primitive(NoneCvec { sort: self.clone() });
        info.add_primitive(SomeCvec { sort: self.clone() });
        info.add_primitive(MergeCvecs { sort: self.clone() });
    }
}

struct NoneCvec {
    sort: Arc<CvecSort>,
}

impl PrimitiveLike for NoneCvec {
    fn name(&self) -> Symbol {
        NONE_CVEC_IDENTIFIER.into()
    }

    fn get_type_constraints(
        &self,
        span: &egglog::ast::Span,
    ) -> Box<dyn egglog::constraint::TypeConstraint> {
        SimpleTypeConstraint::new(self.name(), vec![self.sort.clone()], span.clone()).into_box()
    }

    fn apply(
        &self,
        values: &[egglog::Value],
        _sorts: (&[egglog::ArcSort], &egglog::ArcSort),
        _egraph: Option<&mut egglog::EGraph>,
    ) -> Option<egglog::Value> {
        assert!(values.is_empty());
        let none_cvec_value = to_cvec_val(NONE_CVEC_IDENTIFIER.into());
        Some(none_cvec_value)
    }
}

struct SomeCvec {
    sort: Arc<CvecSort>,
}

impl PrimitiveLike for SomeCvec {
    fn name(&self) -> Symbol {
        "SomeCvec".into()
    }

    // (SomeCvec String)
    fn get_type_constraints(
        &self,
        span: &egglog::ast::Span,
    ) -> Box<dyn egglog::constraint::TypeConstraint> {
        SimpleTypeConstraint::new(
            self.name(),
            vec![Arc::new(egglog::sort::StringSort), self.sort.clone()],
            span.clone(),
        )
        .into_box()
    }

    fn apply(
        &self,
        values: &[egglog::Value],
        _sorts: (&[egglog::ArcSort], &egglog::ArcSort),
        _egraph: Option<&mut egglog::EGraph>,
    ) -> Option<egglog::Value> {
        assert_eq!(values.len(), 1);
        let cvecs = &mut *self.sort.cvecs.lock().unwrap();
        let param_str = Symbol::load(&egglog::sort::StringSort, &values[0]).to_string();
        if param_str == "NoneCvec" {
            panic!("SomeCvec called on NoneCvec");
        }
        let param = to_cvec_val(param_str.clone().into());
        cvecs.insert(param, param_str);
        Some(param)
    }
}

struct MergeCvecs {
    sort: Arc<CvecSort>,
}

impl PrimitiveLike for MergeCvecs {
    fn name(&self) -> Symbol {
        "MergeCvecs".into()
    }

    // (MergeCvecs Cvec Cvec)
    fn get_type_constraints(
        &self,
        span: &egglog::ast::Span,
    ) -> Box<dyn egglog::constraint::TypeConstraint> {
        SimpleTypeConstraint::new(
            self.name(),
            vec![self.sort.clone(), self.sort.clone(), self.sort.clone()],
            span.clone(),
        )
        .into_box()
    }

    fn apply(
        &self,
        values: &[egglog::Value],
        _sorts: (&[egglog::ArcSort], &egglog::ArcSort),
        _egraph: Option<&mut egglog::EGraph>,
    ) -> Option<egglog::Value> {
        assert_eq!(values.len(), 2);
        let cvecs = &mut *self.sort.cvecs.lock().unwrap();
        let first_cvec_hash: String = cvecs.get(&values[0]).unwrap().to_string();

        if first_cvec_hash == NONE_CVEC_IDENTIFIER {
            Some(values[1].clone())
        } else {
            Some(values[0].clone())
        }
    }
}

#[test]
pub fn none_ctor() {
    let mut egraph = EGraph::default();
    egraph
        .add_arcsort(Arc::new(CvecSort::new()), Span::Panic)
        .unwrap();

    let res = egraph
        .parse_and_run_program(
            None,
            r#"
            (let x (NoneCvec))
            (let y (NoneCvec))
            (check (= x y))
            (extract x)
        "#,
        )
        .unwrap();

    assert_eq!(res.len(), 1);
    assert_eq!(
        Sexp::from_str(res[0].as_str()).unwrap(),
        Sexp::from_str("(NoneCvec)").unwrap()
    );
}

#[test]
pub fn some_ctor() {
    let mut egraph = EGraph::default();
    egraph
        .add_arcsort(Arc::new(CvecSort::new()), Span::Panic)
        .unwrap();

    let res = egraph
        .parse_and_run_program(
            None,
            r#"
        (let x (SomeCvec "hello"))
        (let y (SomeCvec "hello"))
        (let z (NoneCvec))
        (check (= x y))
        (check (!= x z))
        (extract x)
    "#,
        )
        .unwrap();

    assert_eq!(res.len(), 1);
    assert_eq!(
        Sexp::from_str(res[0].as_str()).unwrap(),
        Sexp::from_str("(SomeCvec \"hello\")").unwrap()
    );
}

#[test]
pub fn merge_ctor() {
    let mut egraph = EGraph::default();
    egraph
        .add_arcsort(Arc::new(CvecSort::new()), Span::Panic)
        .unwrap();

    let res = egraph
        .parse_and_run_program(
            None,
            r#"
        (let x (NoneCvec))
        (let y (SomeCvec "hello"))
        (let z (MergeCvecs x y))


        (datatype Term
            (Const i64))

        (function HasCvecHash (Term) Cvec :merge (MergeCvecs old new))

        (let t1 (Const 1))
        (let t2 (Const 2))

        (set (HasCvecHash t1) (SomeCvec "[Some(1), Some(1), Some(1), Some(1), Some(1), Some(1), Some(1), Some(1), Some(1), Some(1)]"))
        (set (HasCvecHash t2) (SomeCvec "[Some(1), Some(1), Some(1), Some(1), Some(1), Some(1), Some(1), Some(1), Some(1), Some(1)]"))

        (rule
            ((= (HasCvecHash ?t1) (HasCvecHash ?t2))
             (!= ?t1 ?t2))
            ((extract ?t1)))

            (run 10)

        (check (= (HasCvecHash t1) (HasCvecHash t2)))

        (check (= y z))
        (check (!= x z))
        (extract z)
    "#,
        )
        .unwrap();

    println!("res: {:?}", res);

    assert_eq!(res.len(), 1);
    assert_eq!(
        Sexp::from_str(res[0].as_str()).unwrap(),
        Sexp::from_str("(SomeCvec \"hello\")").unwrap()
    );
}
