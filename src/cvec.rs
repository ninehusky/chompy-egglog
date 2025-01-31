use std::sync::{Arc, Mutex};

use egglog::{
    ast::Symbol,
    constraint::SimpleTypeConstraint,
    sort::{FromSort, Sort, StringSort},
    util::IndexMap,
    PrimitiveLike, Value,
};

const NONE_CVEC_IDENTIFIER: &str = "NoneCvec";

type CvecMap = IndexMap<Value, String>;

/// Wow, I can't believe we're back to creating this!

#[derive(Debug)]
pub struct CvecSort {
    cvecs: Mutex<CvecMap>,
}

impl CvecSort {
    pub fn new() -> Self {
        let mut cvecs: CvecMap = Default::default();
        let none_sym: Symbol = NONE_CVEC_IDENTIFIER.into();
        cvecs.insert(Value::from(none_sym), NONE_CVEC_IDENTIFIER.to_string());
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
        _value: egglog::Value,
        _extractor: &egglog::extract::Extractor,
        _termdag: &mut egglog::TermDag,
    ) -> Option<(egglog::extract::Cost, egglog::Term)> {
        todo!()
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
        "NoneCvec".into()
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
        let none_sym: Symbol = "None".into();
        Some(Value::from(none_sym))
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
        let param = Symbol::load(&StringSort, &values[0]).to_string();
        println!("param: {}", param);
        if param == "NoneCvec" {
            panic!("SomeCvec called on NoneCvec");
        }
        cvecs.insert(values[0].clone(), param.clone());
        let string_sym: Symbol = param.into();
        Some(Value::from(string_sym))
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
