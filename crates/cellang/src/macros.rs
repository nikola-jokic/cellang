use crate::error::RuntimeError;
use crate::hir::expr::{Atom as HirAtom, Expr as HirExpr};
use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;

#[derive(
    Clone,
    Copy,
    Debug,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Hash,
    Serialize,
    Deserialize,
)]
#[serde(rename_all = "snake_case")]
pub enum MacroKind {
    Has,
    All,
    Exists,
    ExistsOne,
    Map,
    Filter,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct MacroRegistry {
    enabled: BTreeSet<MacroKind>,
}

impl MacroRegistry {
    pub fn new() -> Self {
        let mut registry = MacroRegistry::default();
        registry.enable(MacroKind::Has);
        registry.enable(MacroKind::All);
        registry.enable(MacroKind::Exists);
        registry.enable(MacroKind::ExistsOne);
        registry.enable(MacroKind::Map);
        registry.enable(MacroKind::Filter);
        registry
    }

    pub fn empty() -> Self {
        MacroRegistry {
            enabled: BTreeSet::new(),
        }
    }

    pub fn enable(&mut self, kind: MacroKind) {
        self.enabled.insert(kind);
    }

    pub fn disable(&mut self, kind: MacroKind) {
        self.enabled.remove(&kind);
    }

    pub fn is_enabled(&self, kind: MacroKind) -> bool {
        self.enabled.contains(&kind)
    }

    pub fn merge(&mut self, other: &MacroRegistry) {
        for kind in &other.enabled {
            self.enabled.insert(*kind);
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ComprehensionKind {
    All,
    Exists,
    ExistsOne,
    Map,
    Filter,
}

#[derive(Clone, Debug)]
pub enum MacroInvocation {
    Has {
        target: HirExpr,
        field: String,
    },
    Comprehension {
        kind: ComprehensionKind,
        range: HirExpr,
        var: String,
        predicate: Option<HirExpr>,
        transform: Option<HirExpr>,
    },
}

pub fn detect_macro_call(
    registry: &MacroRegistry,
    func: &HirExpr,
    args: &[HirExpr],
    is_method: bool,
) -> Result<Option<MacroInvocation>, RuntimeError> {
    let name = resolve_function_name(func)?;

    let invocation = match name.as_str() {
        "has" if registry.is_enabled(MacroKind::Has) => {
            Some(parse_has_macro(args, is_method)?)
        }
        "all" if registry.is_enabled(MacroKind::All) => {
            Some(parse_comprehension(
                ComprehensionKind::All,
                &name,
                args,
                ExpectedArity::Fixed(3),
            )?)
        }
        "exists" if registry.is_enabled(MacroKind::Exists) => {
            Some(parse_comprehension(
                ComprehensionKind::Exists,
                &name,
                args,
                ExpectedArity::Fixed(3),
            )?)
        }
        "exists_one" if registry.is_enabled(MacroKind::ExistsOne) => {
            Some(parse_comprehension(
                ComprehensionKind::ExistsOne,
                &name,
                args,
                ExpectedArity::Fixed(3),
            )?)
        }
        "map" if registry.is_enabled(MacroKind::Map) => {
            Some(parse_comprehension(
                ComprehensionKind::Map,
                &name,
                args,
                ExpectedArity::Either(3, 4),
            )?)
        }
        "filter" if registry.is_enabled(MacroKind::Filter) => {
            Some(parse_comprehension(
                ComprehensionKind::Filter,
                &name,
                args,
                ExpectedArity::Fixed(3),
            )?)
        }
        _ => None,
    };
    Ok(invocation)
}

fn resolve_function_name(expr: &HirExpr) -> Result<String, RuntimeError> {
    match expr {
        HirExpr::Atom(HirAtom::Ident(name)) => Ok(name.clone()),
        HirExpr::Field { target, field } => {
            let left = resolve_function_name(target)?;
            Ok(format!("{}.{}", left, field))
        }
        _ => Err(RuntimeError::new(
            "function calls must reference an identifier",
        )),
    }
}

enum ExpectedArity {
    Fixed(usize),
    Either(usize, usize),
}

fn parse_has_macro(
    args: &[HirExpr],
    is_method: bool,
) -> Result<MacroInvocation, RuntimeError> {
    if is_method {
        return Err(RuntimeError::new(
            "has() macro must be invoked as a standalone function",
        ));
    }
    if args.len() != 1 {
        return Err(RuntimeError::new(
            "has() macro expects a single field selection argument",
        ));
    }
    let HirExpr::Field { target, field } = &args[0] else {
        return Err(RuntimeError::new(
            "has() macro argument must be a field selection",
        ));
    };
    Ok(MacroInvocation::Has {
        target: (**target).clone(),
        field: field.clone(),
    })
}

fn parse_comprehension(
    kind: ComprehensionKind,
    macro_name: &str,
    args: &[HirExpr],
    arity: ExpectedArity,
) -> Result<MacroInvocation, RuntimeError> {
    let len_ok = match arity {
        ExpectedArity::Fixed(size) => args.len() == size,
        ExpectedArity::Either(a, b) => args.len() == a || args.len() == b,
    };
    if !len_ok {
        return Err(RuntimeError::new(format!(
            "Macro '{macro_name}' received unexpected number of arguments"
        )));
    }

    let range = args
        .first()
        .ok_or_else(|| RuntimeError::new("macro invocation missing range"))?;
    let binder_expr = args.get(1).ok_or_else(|| {
        RuntimeError::new("macro invocation missing iterator variable")
    })?;
    let var = ident_name(binder_expr).ok_or_else(|| {
        RuntimeError::new(format!(
            "Macro '{macro_name}' iterator variable must be an identifier"
        ))
    })?;

    let (predicate, transform) = match kind {
        ComprehensionKind::Map => match args.len() {
            3 => (None, Some(&args[2])),
            4 => (Some(&args[2]), Some(&args[3])),
            _ => unreachable!(),
        },
        _ => (Some(&args[2]), None),
    };

    if matches!(kind, ComprehensionKind::Map) && transform.is_none() {
        return Err(RuntimeError::new(
            "map() macro requires a transform expression",
        ));
    }

    if predicate.is_none() && !matches!(kind, ComprehensionKind::Map) {
        return Err(RuntimeError::new(format!(
            "Macro '{macro_name}' requires a predicate expression"
        )));
    }

    Ok(MacroInvocation::Comprehension {
        kind,
        range: range.clone(),
        var,
        predicate: predicate.cloned(),
        transform: transform.cloned(),
    })
}

fn ident_name(expr: &HirExpr) -> Option<String> {
    match expr {
        HirExpr::Atom(HirAtom::Ident(name)) => Some(name.clone()),
        _ => None,
    }
}
