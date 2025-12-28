use crate::error::RuntimeError;
use crate::parser::{Atom, Op, TokenTree};
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
    /// Creates a new MacroRegistry with all macros enabled.
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

    /// Creates a new MacroRegistry with no macros enabled.
    pub fn empty() -> Self {
        MacroRegistry {
            enabled: BTreeSet::new(),
        }
    }

    /// Enables a macro of the given kind.
    pub fn enable(&mut self, kind: MacroKind) {
        self.enabled.insert(kind);
    }

    /// Disables a macro of the given kind.
    pub fn disable(&mut self, kind: MacroKind) {
        self.enabled.remove(&kind);
    }

    /// Checks if a macro of the given kind is enabled.
    pub fn is_enabled(&self, kind: MacroKind) -> bool {
        self.enabled.contains(&kind)
    }

    /// Merges another MacroRegistry into this one, enabling any macros that are
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

#[derive(Clone, Copy, Debug)]
pub enum MacroInvocation<'src> {
    Has {
        target: &'src TokenTree<'src>,
        field: &'src str,
    },
    Comprehension {
        kind: ComprehensionKind,
        range: &'src TokenTree<'src>,
        var: &'src str,
        predicate: Option<&'src TokenTree<'src>>,
        transform: Option<&'src TokenTree<'src>>,
    },
}

pub fn detect_macro_call<'src>(
    registry: &MacroRegistry,
    name: &str,
    args: &'src [TokenTree<'src>],
    is_method: bool,
) -> Result<Option<MacroInvocation<'src>>, RuntimeError> {
    let invocation = match name {
        "has" if registry.is_enabled(MacroKind::Has) => {
            Some(parse_has_macro(args, is_method)?)
        }
        "all" if registry.is_enabled(MacroKind::All) => {
            Some(parse_comprehension(
                ComprehensionKind::All,
                name,
                args,
                ExpectedArity::Fixed(3),
            )?)
        }
        "exists" if registry.is_enabled(MacroKind::Exists) => {
            Some(parse_comprehension(
                ComprehensionKind::Exists,
                name,
                args,
                ExpectedArity::Fixed(3),
            )?)
        }
        "exists_one" if registry.is_enabled(MacroKind::ExistsOne) => {
            Some(parse_comprehension(
                ComprehensionKind::ExistsOne,
                name,
                args,
                ExpectedArity::Fixed(3),
            )?)
        }
        "map" if registry.is_enabled(MacroKind::Map) => {
            Some(parse_comprehension(
                ComprehensionKind::Map,
                name,
                args,
                ExpectedArity::Either(3, 4),
            )?)
        }
        "filter" if registry.is_enabled(MacroKind::Filter) => {
            Some(parse_comprehension(
                ComprehensionKind::Filter,
                name,
                args,
                ExpectedArity::Fixed(3),
            )?)
        }
        _ => None,
    };
    Ok(invocation)
}

enum ExpectedArity {
    Fixed(usize),
    Either(usize, usize),
}

fn parse_has_macro<'src>(
    args: &'src [TokenTree<'src>],
    is_method: bool,
) -> Result<MacroInvocation<'src>, RuntimeError> {
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
    let TokenTree::Cons(Op::Field, nodes) = &args[0] else {
        return Err(RuntimeError::new(
            "has() macro argument must be a field selection",
        ));
    };
    if nodes.len() != 2 {
        return Err(RuntimeError::new("has() macro argument is malformed"));
    }
    let Some(field) = ident_name(&nodes[1]) else {
        return Err(RuntimeError::new(
            "has() macro field accessor must be an identifier",
        ));
    };
    Ok(MacroInvocation::Has {
        target: &nodes[0],
        field,
    })
}

fn parse_comprehension<'src>(
    kind: ComprehensionKind,
    macro_name: &str,
    args: &'src [TokenTree<'src>],
    arity: ExpectedArity,
) -> Result<MacroInvocation<'src>, RuntimeError> {
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
    let Some(var) = ident_name(binder_expr) else {
        return Err(RuntimeError::new(format!(
            "Macro '{macro_name}' iterator variable must be an identifier"
        )));
    };

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
        range,
        var,
        predicate,
        transform,
    })
}

fn ident_name<'src>(expr: &'src TokenTree<'src>) -> Option<&'src str> {
    match expr {
        TokenTree::Atom(Atom::Ident(name)) => Some(name),
        _ => None,
    }
}
