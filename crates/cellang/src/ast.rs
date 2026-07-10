//! Type checking layer: Semantic analysis and typed AST construction.
//!
//! This module forms the **third stage** of the CEL pipeline:
//! CST (`crate::syntax`) → HIR (`crate::hir`) → Type Check (this module) → Eval (`crate::interpreter`)
//!
//! The type checker validates HIR expressions against the runtime's declared types and produces
//! a fully typed `TypedExpr` graph suitable for evaluation. Type checking enforces CEL's type
//! rules (function overload resolution, type assignability, etc.) and reports type errors
//! during this phase rather than at runtime.
//!
//! **Module boundary**: This module is internal to the parser pipeline. External code should use
//! the public API facade at `crate::parser::type_check` rather than importing directly from
//! this module.

use crate::env::Env;
use crate::error::RuntimeError;
use crate::hir::expr::{
    Atom as HirAtom, BinaryOp as HirBinaryOp, Expr as HirExpr,
    UnaryOp as HirUnaryOp,
};
use crate::macros::{self, ComprehensionKind, MacroInvocation};
use crate::types::{
    FunctionDecl, NamedType, OverloadDecl, Type, TypeName, is_assignable,
    is_dyn_like,
};
use serde::{Deserialize, Serialize};

/// Fully typed expression tree produced after semantic analysis.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct TypedExpr {
    pub ty: Type,
    pub expr: ExprKind,
}

impl TypedExpr {
    fn new(ty: Type, expr: ExprKind) -> Self {
        Self { ty, expr }
    }
}

#[derive(Default)]
struct TypeScope {
    bindings: Vec<(String, Type)>,
}

impl TypeScope {
    fn push(&mut self, name: impl Into<String>, ty: Type) {
        self.bindings.push((name.into(), ty));
    }

    fn pop(&mut self) {
        self.bindings.pop();
    }

    fn lookup(&self, name: &str) -> Option<&Type> {
        self.bindings
            .iter()
            .rev()
            .find(|(binding, _)| binding == name)
            .map(|(_, ty)| ty)
    }
}

/// Logical structure of a typed AST node.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum ExprKind {
    Literal(LiteralValue),
    Ident {
        name: String,
    },
    List {
        elements: Vec<TypedExpr>,
    },
    Map {
        entries: Vec<MapEntry>,
    },
    Unary {
        op: UnaryOp,
        expr: Box<TypedExpr>,
    },
    Binary {
        op: BinaryOp,
        left: Box<TypedExpr>,
        right: Box<TypedExpr>,
    },
    Call {
        function: String,
        args: Vec<TypedExpr>,
        is_method: bool,
    },
    Field {
        target: Box<TypedExpr>,
        accessor: FieldAccessor,
    },
    Index {
        target: Box<TypedExpr>,
        index: Box<TypedExpr>,
    },
    Ternary {
        condition: Box<TypedExpr>,
        then_branch: Box<TypedExpr>,
        else_branch: Box<TypedExpr>,
    },
    Group {
        expr: Box<TypedExpr>,
    },
    Dyn {
        expr: Box<TypedExpr>,
    },
    MacroHas {
        target: Box<TypedExpr>,
        field: String,
    },
    MacroComprehension {
        comprehension: ComprehensionKind,
        range: Box<TypedExpr>,
        var: String,
        predicate: Option<Box<TypedExpr>>,
        transform: Option<Box<TypedExpr>>,
    },
}

/// Describes how a field is accessed (static `foo.bar` vs dynamic `foo[field]`).
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "accessor", rename_all = "snake_case")]
pub enum FieldAccessor {
    Static { name: String },
    Dynamic { expr: Box<TypedExpr> },
}

/// Key/value pair inside a typed map literal.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct MapEntry {
    pub key: TypedExpr,
    pub value: TypedExpr,
}

/// Literal payloads captured inside [`ExprKind::Literal`].
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "literal", content = "value", rename_all = "snake_case")]
pub enum LiteralValue {
    Bool(bool),
    Int(i64),
    Uint(u64),
    Double(f64),
    String(String),
    Bytes(Vec<u8>),
    Null,
}

/// Supported unary operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum UnaryOp {
    Not,
    Neg,
}

/// Supported binary operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum BinaryOp {
    Add,
    Subtract,
    Multiply,
    Divide,
    Modulo,
    And,
    Or,
    Equal,
    NotEqual,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
    In,
}

/// Performs semantic analysis over the parsed HIR expression and produces a typed
/// expression graph that can be serialized and cached.
pub fn type_check(
    env: &Env,
    expr: &HirExpr,
) -> Result<TypedExpr, RuntimeError> {
    let mut scope = TypeScope::default();
    infer_expr(env, &mut scope, expr)
}

fn infer_expr(
    env: &Env,
    scope: &mut TypeScope,
    expr: &HirExpr,
) -> Result<TypedExpr, RuntimeError> {
    match expr {
        HirExpr::Atom(atom) => infer_atom(env, scope, atom),
        HirExpr::Unary { op, expr: inner } => {
            infer_unary(env, scope, *op, inner)
        }
        HirExpr::Binary { op, lhs, rhs } => {
            infer_binary(env, scope, *op, lhs, rhs)
        }
        HirExpr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => infer_ternary(env, scope, cond, then_expr, else_expr),
        HirExpr::Call {
            func,
            args,
            is_method,
        } => infer_call(env, scope, func, args, *is_method),
        HirExpr::Field { target, field } => {
            infer_field_access(env, scope, target, field)
        }
        HirExpr::Index { target, index } => {
            infer_index_access(env, scope, target, index)
        }
        HirExpr::List(elements) => infer_list_literal(env, scope, elements),
        HirExpr::Map(entries) => infer_map_literal(env, scope, entries),
        HirExpr::Group(inner) => {
            let typed = infer_expr(env, scope, inner)?;
            let ty = typed.ty.clone();
            Ok(TypedExpr::new(
                ty,
                ExprKind::Group {
                    expr: Box::new(typed),
                },
            ))
        }
        HirExpr::Dyn(inner) => {
            let typed = infer_expr(env, scope, inner)?;
            Ok(TypedExpr::new(
                Type::Dyn,
                ExprKind::Dyn {
                    expr: Box::new(typed),
                },
            ))
        }
    }
}

fn infer_atom(
    env: &Env,
    scope: &mut TypeScope,
    atom: &HirAtom,
) -> Result<TypedExpr, RuntimeError> {
    let expr = match atom {
        HirAtom::Bool(value) => TypedExpr::new(
            Type::Bool,
            ExprKind::Literal(LiteralValue::Bool(*value)),
        ),
        HirAtom::Int(value) => TypedExpr::new(
            Type::Int,
            ExprKind::Literal(LiteralValue::Int(*value)),
        ),
        HirAtom::Uint(value) => TypedExpr::new(
            Type::Uint,
            ExprKind::Literal(LiteralValue::Uint(*value)),
        ),
        HirAtom::Double(value) => TypedExpr::new(
            Type::Double,
            ExprKind::Literal(LiteralValue::Double(*value)),
        ),
        HirAtom::String(value) => TypedExpr::new(
            Type::String,
            ExprKind::Literal(LiteralValue::String(value.clone())),
        ),
        HirAtom::Bytes(value) => TypedExpr::new(
            Type::Bytes,
            ExprKind::Literal(LiteralValue::Bytes(value.clone())),
        ),
        HirAtom::Null => {
            TypedExpr::new(Type::Null, ExprKind::Literal(LiteralValue::Null))
        }
        HirAtom::Ident(name) => {
            if let Some(local) = scope.lookup(name) {
                return Ok(TypedExpr::new(
                    local.clone(),
                    ExprKind::Ident { name: name.clone() },
                ));
            }
            let decl = env
                .lookup_ident(name)
                .ok_or_else(|| RuntimeError::missing_identifier(name))?;
            TypedExpr::new(
                decl.ty.clone(),
                ExprKind::Ident { name: name.clone() },
            )
        }
    };
    Ok(expr)
}

fn infer_unary(
    env: &Env,
    scope: &mut TypeScope,
    op: HirUnaryOp,
    expr: &HirExpr,
) -> Result<TypedExpr, RuntimeError> {
    let typed_expr = infer_expr(env, scope, expr)?;
    match op {
        HirUnaryOp::Not => {
            expect_boolean(&typed_expr.ty, "logical not")?;
            Ok(TypedExpr::new(
                Type::Bool,
                ExprKind::Unary {
                    op: UnaryOp::Not,
                    expr: Box::new(typed_expr),
                },
            ))
        }
        HirUnaryOp::Neg => {
            let result_ty =
                numeric_unary_result(&typed_expr.ty, "unary minus")?;
            Ok(TypedExpr::new(
                result_ty,
                ExprKind::Unary {
                    op: UnaryOp::Neg,
                    expr: Box::new(typed_expr),
                },
            ))
        }
    }
}

fn infer_binary(
    env: &Env,
    scope: &mut TypeScope,
    op: HirBinaryOp,
    lhs: &HirExpr,
    rhs: &HirExpr,
) -> Result<TypedExpr, RuntimeError> {
    let left = infer_expr(env, scope, lhs)?;
    let right = infer_expr(env, scope, rhs)?;

    match op {
        HirBinaryOp::Add => {
            let ty = infer_addition_type(&left.ty, &right.ty)?;
            Ok(make_binary(BinaryOp::Add, ty, left, right))
        }
        HirBinaryOp::Sub => {
            let ty = numeric_binary_result(
                &left.ty,
                &right.ty,
                NumericBinaryOp::Subtract,
            )?;
            Ok(make_binary(BinaryOp::Subtract, ty, left, right))
        }
        HirBinaryOp::Mul => {
            let ty = numeric_binary_result(
                &left.ty,
                &right.ty,
                NumericBinaryOp::Multiply,
            )?;
            Ok(make_binary(BinaryOp::Multiply, ty, left, right))
        }
        HirBinaryOp::Div => {
            let ty = numeric_binary_result(
                &left.ty,
                &right.ty,
                NumericBinaryOp::Divide,
            )?;
            Ok(make_binary(BinaryOp::Divide, ty, left, right))
        }
        HirBinaryOp::Mod => {
            let ty = numeric_binary_result(
                &left.ty,
                &right.ty,
                NumericBinaryOp::Modulo,
            )?;
            Ok(make_binary(BinaryOp::Modulo, ty, left, right))
        }
        HirBinaryOp::And => {
            expect_boolean(&left.ty, "logical and")?;
            expect_boolean(&right.ty, "logical and")?;
            Ok(make_binary(BinaryOp::And, Type::Bool, left, right))
        }
        HirBinaryOp::Or => {
            expect_boolean(&left.ty, "logical or")?;
            expect_boolean(&right.ty, "logical or")?;
            Ok(make_binary(BinaryOp::Or, Type::Bool, left, right))
        }
        HirBinaryOp::Eq => {
            Ok(make_binary(BinaryOp::Equal, Type::Bool, left, right))
        }
        HirBinaryOp::Ne => {
            Ok(make_binary(BinaryOp::NotEqual, Type::Bool, left, right))
        }
        HirBinaryOp::Lt => {
            ensure_comparable(&left.ty, &right.ty, "less than")?;
            Ok(make_binary(BinaryOp::Less, Type::Bool, left, right))
        }
        HirBinaryOp::Le => {
            ensure_comparable(&left.ty, &right.ty, "less than or equal")?;
            Ok(make_binary(BinaryOp::LessEqual, Type::Bool, left, right))
        }
        HirBinaryOp::Gt => {
            ensure_comparable(&left.ty, &right.ty, "greater than")?;
            Ok(make_binary(BinaryOp::Greater, Type::Bool, left, right))
        }
        HirBinaryOp::Ge => {
            ensure_comparable(&left.ty, &right.ty, "greater than or equal")?;
            Ok(make_binary(BinaryOp::GreaterEqual, Type::Bool, left, right))
        }
        HirBinaryOp::In => infer_in_operator(env, scope, lhs, rhs),
    }
}

fn infer_ternary(
    env: &Env,
    scope: &mut TypeScope,
    cond: &HirExpr,
    then_expr: &HirExpr,
    else_expr: &HirExpr,
) -> Result<TypedExpr, RuntimeError> {
    let condition = infer_expr(env, scope, cond)?;
    expect_boolean(&condition.ty, "ternary condition")?;
    let then_branch = infer_expr(env, scope, then_expr)?;
    let else_branch = infer_expr(env, scope, else_expr)?;
    let ty = unify_types(then_branch.ty.clone(), else_branch.ty.clone())?;
    Ok(TypedExpr::new(
        ty,
        ExprKind::Ternary {
            condition: Box::new(condition),
            then_branch: Box::new(then_branch),
            else_branch: Box::new(else_branch),
        },
    ))
}

fn infer_list_literal(
    env: &Env,
    scope: &mut TypeScope,
    elements: &[HirExpr],
) -> Result<TypedExpr, RuntimeError> {
    if elements.is_empty() {
        return Ok(TypedExpr::new(
            Type::list(Type::Dyn),
            ExprKind::List {
                elements: Vec::new(),
            },
        ));
    }
    let mut element_ty = None;
    let mut typed_elements = Vec::with_capacity(elements.len());
    for expr in elements {
        let typed = infer_expr(env, scope, expr)?;
        element_ty = match element_ty {
            Some(current) => Some(unify_types(current, typed.ty.clone())?),
            None => Some(typed.ty.clone()),
        };
        typed_elements.push(typed);
    }
    let elem_ty = element_ty.unwrap_or(Type::Dyn);
    Ok(TypedExpr::new(
        Type::list(elem_ty),
        ExprKind::List {
            elements: typed_elements,
        },
    ))
}

fn infer_map_literal(
    env: &Env,
    scope: &mut TypeScope,
    entries: &[(HirExpr, HirExpr)],
) -> Result<TypedExpr, RuntimeError> {
    if entries.is_empty() {
        return Ok(TypedExpr::new(
            Type::map(Type::Dyn, Type::Dyn),
            ExprKind::Map {
                entries: Vec::new(),
            },
        ));
    }
    let mut key_ty = None;
    let mut value_ty = None;
    let mut typed_entries = Vec::with_capacity(entries.len());
    for (key_expr, value_expr) in entries {
        let key = infer_expr(env, scope, key_expr)?;
        let value = infer_expr(env, scope, value_expr)?;
        key_ty = match key_ty {
            Some(current) => Some(unify_types(current, key.ty.clone())?),
            None => Some(key.ty.clone()),
        };
        value_ty = match value_ty {
            Some(current) => Some(unify_types(current, value.ty.clone())?),
            None => Some(value.ty.clone()),
        };
        typed_entries.push(MapEntry { key, value });
    }
    Ok(TypedExpr::new(
        Type::map(key_ty.unwrap(), value_ty.unwrap()),
        ExprKind::Map {
            entries: typed_entries,
        },
    ))
}

fn infer_field_access(
    env: &Env,
    scope: &mut TypeScope,
    target_expr: &HirExpr,
    field: &str,
) -> Result<TypedExpr, RuntimeError> {
    let target = infer_expr(env, scope, target_expr)?;
    let accessor = FieldAccessor::Static {
        name: field.to_string(),
    };
    let ty = match (&target.ty, &accessor) {
        (ty, _) if is_dyn_like(ty) => Type::Dyn,
        (Type::Struct(name), FieldAccessor::Static { name: field }) => {
            struct_field_type(env, name, field)?
        }
        (Type::Map(key_ty, value_ty), FieldAccessor::Static { .. }) => {
            if !is_assignable(&Type::String, key_ty) && !is_dyn_like(key_ty) {
                return Err(RuntimeError::new(format!(
                    "Map field access requires string keys but found {}",
                    describe_type(key_ty)
                )));
            }
            (**value_ty).clone()
        }
        (Type::Null, _) => {
            return Err(RuntimeError::new("Cannot access fields on null"));
        }
        (other, _) => {
            return Err(RuntimeError::new(format!(
                "Field access is not supported on values of kind {}",
                describe_type(other)
            )));
        }
    };
    Ok(TypedExpr::new(
        ty,
        ExprKind::Field {
            target: Box::new(target),
            accessor,
        },
    ))
}

fn infer_index_access(
    env: &Env,
    scope: &mut TypeScope,
    target_expr: &HirExpr,
    index_expr: &HirExpr,
) -> Result<TypedExpr, RuntimeError> {
    let target = infer_expr(env, scope, target_expr)?;
    let index = infer_expr(env, scope, index_expr)?;
    let ty = match &target.ty {
        ty if is_dyn_like(ty) => Type::Dyn,
        Type::List(element) => {
            ensure_index_operand(&index.ty, "list")?;
            (**element).clone()
        }
        Type::String => {
            ensure_index_operand(&index.ty, "string")?;
            Type::String
        }
        Type::Bytes => {
            ensure_index_operand(&index.ty, "bytes")?;
            Type::Uint
        }
        Type::Map(key_ty, value_ty) => {
            if !is_assignable(key_ty, &index.ty) {
                return Err(RuntimeError::new(format!(
                    "Map index expects type {} but found {}",
                    describe_type(key_ty),
                    describe_type(&index.ty)
                )));
            }
            (**value_ty).clone()
        }
        Type::Struct(name) => {
            if let HirExpr::Atom(HirAtom::String(field)) = index_expr {
                struct_field_type(env, name, field)?
            } else {
                Type::Dyn
            }
        }
        Type::Null => {
            return Err(RuntimeError::new("Cannot index null"));
        }
        other => {
            return Err(RuntimeError::new(format!(
                "Index operator is not supported for values of kind {}",
                describe_type(other)
            )));
        }
    };
    Ok(TypedExpr::new(
        ty,
        ExprKind::Index {
            target: Box::new(target),
            index: Box::new(index),
        },
    ))
}

fn infer_in_operator(
    env: &Env,
    scope: &mut TypeScope,
    needle_expr: &HirExpr,
    haystack_expr: &HirExpr,
) -> Result<TypedExpr, RuntimeError> {
    let needle = infer_expr(env, scope, needle_expr)?;
    let haystack = infer_expr(env, scope, haystack_expr)?;
    match &haystack.ty {
        Type::List(element) => {
            if !is_assignable(element, &needle.ty) && !is_dyn_like(&needle.ty) {
                return Err(RuntimeError::new(format!(
                    "Operator 'in' expects element type {} but found {}",
                    describe_type(element),
                    describe_type(&needle.ty)
                )));
            }
        }
        Type::Map(key_ty, _) => {
            if !is_assignable(key_ty, &needle.ty) && !is_dyn_like(&needle.ty) {
                return Err(RuntimeError::new(format!(
                    "Operator 'in' expects key type {} but found {}",
                    describe_type(key_ty),
                    describe_type(&needle.ty)
                )));
            }
        }
        Type::String => {
            if !is_assignable(&Type::String, &needle.ty)
                && !is_dyn_like(&needle.ty)
            {
                return Err(RuntimeError::new(
                    "String containment expects a string needle",
                ));
            }
        }
        Type::Bytes => {
            if !is_assignable(&Type::Bytes, &needle.ty)
                && !is_dyn_like(&needle.ty)
            {
                return Err(RuntimeError::new(
                    "Bytes containment expects a bytes needle",
                ));
            }
        }
        ty if is_dyn_like(ty) => {}
        other => {
            return Err(RuntimeError::new(format!(
                "Operator 'in' is not supported for values of kind {}",
                describe_type(other)
            )));
        }
    }
    Ok(make_binary(BinaryOp::In, Type::Bool, needle, haystack))
}

fn infer_call(
    env: &Env,
    scope: &mut TypeScope,
    func: &HirExpr,
    args: &[HirExpr],
    is_method: bool,
) -> Result<TypedExpr, RuntimeError> {
    let name = resolve_hir_function_name(func).ok_or_else(|| {
        RuntimeError::new("function calls must reference an identifier")
    })?;
    if let Some(invocation) =
        macros::detect_macro_call(env.macros(), func, args, is_method)?
    {
        return infer_macro_call(env, scope, invocation);
    }
    let decl = env.lookup_function(&name).ok_or_else(|| {
        RuntimeError::new(format!(
            "Function '{name}' is not declared in the environment"
        ))
    })?;
    let typed_args = args
        .iter()
        .map(|expr| infer_expr(env, scope, expr))
        .collect::<Result<Vec<_>, _>>()?;
    let arg_types = typed_args
        .iter()
        .map(|expr| expr.ty.clone())
        .collect::<Vec<_>>();
    if let Some(overload) = select_overload(decl, &arg_types, is_method) {
        return Ok(TypedExpr::new(
            overload.result.clone(),
            ExprKind::Call {
                function: name,
                args: typed_args,
                is_method,
            },
        ));
    }
    Err(RuntimeError::new(format!(
        "Function '{}' does not have an overload matching arguments ({})",
        name,
        format_type_list(&arg_types)
    )))
}

fn resolve_hir_function_name(expr: &HirExpr) -> Option<String> {
    match expr {
        HirExpr::Atom(HirAtom::Ident(name)) => Some(name.clone()),
        HirExpr::Field { target, field } => {
            let left = resolve_hir_function_name(target)?;
            Some(format!("{}.{}", left, field))
        }
        _ => None,
    }
}

fn infer_macro_call(
    env: &Env,
    scope: &mut TypeScope,
    invocation: MacroInvocation,
) -> Result<TypedExpr, RuntimeError> {
    match invocation {
        MacroInvocation::Has { target, field } => {
            infer_has_macro(env, scope, &target, &field)
        }
        MacroInvocation::Comprehension {
            kind,
            range,
            var,
            predicate,
            transform,
        } => infer_comprehension_macro(
            env,
            scope,
            kind,
            &range,
            &var,
            predicate.as_ref(),
            transform.as_ref(),
        ),
    }
}

fn infer_has_macro(
    env: &Env,
    scope: &mut TypeScope,
    target_expr: &HirExpr,
    field: &str,
) -> Result<TypedExpr, RuntimeError> {
    let target = infer_expr(env, scope, target_expr)?;
    match &target.ty {
        ty if is_dyn_like(ty) => {}
        Type::Struct(name) => {
            struct_field_type(env, name, field)?;
        }
        Type::Map(key_ty, _) => {
            if !is_assignable(&Type::String, key_ty) && !is_dyn_like(key_ty) {
                return Err(RuntimeError::new(format!(
                    "has() macro requires string-compatible map keys but found {}",
                    describe_type(key_ty)
                )));
            }
        }
        Type::Null => {
            return Err(RuntimeError::new(
                "has() macro cannot operate on null values",
            ));
        }
        other => {
            return Err(RuntimeError::new(format!(
                "has() macro is not supported for values of kind {}",
                describe_type(other)
            )));
        }
    }
    Ok(TypedExpr::new(
        Type::Bool,
        ExprKind::MacroHas {
            target: Box::new(target),
            field: field.to_string(),
        },
    ))
}

fn infer_comprehension_macro(
    env: &Env,
    scope: &mut TypeScope,
    kind: ComprehensionKind,
    range_expr: &HirExpr,
    var: &str,
    predicate_expr: Option<&HirExpr>,
    transform_expr: Option<&HirExpr>,
) -> Result<TypedExpr, RuntimeError> {
    let range = infer_expr(env, scope, range_expr)?;
    let macro_name = comprehension_name(kind);
    let binder_ty = macro_binder_type(macro_name, &range.ty)?;

    scope.push(var, binder_ty.clone());
    let predicate_result: Result<Option<Box<TypedExpr>>, RuntimeError> =
        predicate_expr
            .map(|expr| {
                let typed = infer_expr(env, scope, expr)?;
                expect_boolean(
                    &typed.ty,
                    &format!("{macro_name}() predicate"),
                )?;
                Ok(Box::new(typed))
            })
            .transpose();
    let transform_result: Result<Option<Box<TypedExpr>>, RuntimeError> =
        transform_expr
            .map(|expr| infer_expr(env, scope, expr).map(Box::new))
            .transpose();
    scope.pop();

    let predicate = predicate_result?;
    let transform = transform_result?;

    let result_ty = match kind {
        ComprehensionKind::All
        | ComprehensionKind::Exists
        | ComprehensionKind::ExistsOne => Type::Bool,
        ComprehensionKind::Map => {
            let transform =
                transform.as_ref().expect("map macro transform validated");
            Type::list(transform.ty.clone())
        }
        ComprehensionKind::Filter => Type::list(binder_ty.clone()),
    };

    Ok(TypedExpr::new(
        result_ty,
        ExprKind::MacroComprehension {
            comprehension: kind,
            range: Box::new(range),
            var: var.to_string(),
            predicate,
            transform,
        },
    ))
}

fn macro_binder_type(
    macro_name: &str,
    ty: &Type,
) -> Result<Type, RuntimeError> {
    match ty {
        Type::List(element) => Ok((**element).clone()),
        Type::Map(key, _) => Ok((**key).clone()),
        other if is_dyn_like(other) => Ok(Type::Dyn),
        Type::Null => Err(RuntimeError::new(format!(
            "Macro '{macro_name}' cannot operate on null values",
        ))),
        other => Err(RuntimeError::new(format!(
            "Macro '{macro_name}' expects a list or map but found {}",
            describe_type(other)
        ))),
    }
}

fn comprehension_name(kind: ComprehensionKind) -> &'static str {
    match kind {
        ComprehensionKind::All => "all",
        ComprehensionKind::Exists => "exists",
        ComprehensionKind::ExistsOne => "exists_one",
        ComprehensionKind::Map => "map",
        ComprehensionKind::Filter => "filter",
    }
}

fn select_overload<'a>(
    decl: &'a FunctionDecl,
    arg_types: &[Type],
    is_method: bool,
) -> Option<&'a OverloadDecl> {
    decl.overloads
        .iter()
        .find(|overload| matches_overload(overload, arg_types, is_method))
}

fn matches_overload(
    overload: &OverloadDecl,
    arg_types: &[Type],
    is_method: bool,
) -> bool {
    let (method_receiver, method_args) = if is_method {
        if arg_types.is_empty() {
            return false;
        }
        (Some(&arg_types[0]), &arg_types[1..])
    } else {
        (None, arg_types)
    };

    let (receiver, remaining_args): (Option<&Type>, &[Type]) =
        if overload.receiver.is_some() {
            if let Some(receiver_ty) = method_receiver {
                (Some(receiver_ty), method_args)
            } else if !method_args.is_empty() {
                (Some(&method_args[0]), &method_args[1..])
            } else {
                return false;
            }
        } else {
            if method_receiver.is_some() {
                return false;
            }
            (None, method_args)
        };

    if overload.args.len() != remaining_args.len() {
        return false;
    }

    if let (Some(expected), Some(actual)) =
        (overload.receiver.as_ref(), receiver)
    {
        if !is_assignable(expected, actual) {
            return false;
        }
    } else if overload.receiver.is_some() && receiver.is_none() {
        return false;
    }

    overload
        .args
        .iter()
        .zip(remaining_args.iter())
        .all(|(expected, actual)| is_assignable(expected, actual))
}

fn struct_field_type(
    env: &Env,
    name: &TypeName,
    field: &str,
) -> Result<Type, RuntimeError> {
    let named = env.lookup_type(name).ok_or_else(|| {
        RuntimeError::new(format!(
            "Unknown struct type '{}' referenced in expression",
            name.as_str()
        ))
    })?;
    let NamedType::Struct(strct) = named else {
        return Err(RuntimeError::new(format!(
            "Named type '{}' is not a struct",
            name.as_str()
        )));
    };
    strct
        .fields
        .get(field)
        .map(|field_decl| field_decl.ty.clone())
        .ok_or_else(|| {
            RuntimeError::new(format!(
                "Struct '{}' does not contain field '{}'",
                name.as_str(),
                field
            ))
        })
}

fn infer_addition_type(
    left: &Type,
    right: &Type,
) -> Result<Type, RuntimeError> {
    if is_dyn_like(left) || is_dyn_like(right) {
        return Ok(Type::Dyn);
    }
    match (left, right) {
        (Type::String, Type::String) => Ok(Type::String),
        (Type::Bytes, Type::Bytes) => Ok(Type::Bytes),
        (Type::List(a), Type::List(b)) => {
            let merged = unify_types((**a).clone(), (**b).clone())?;
            Ok(Type::list(merged))
        }
        _ => numeric_binary_result(left, right, NumericBinaryOp::Add),
    }
}

fn expect_boolean(ty: &Type, context: &str) -> Result<(), RuntimeError> {
    if matches!(ty, Type::Bool) || is_dyn_like(ty) {
        Ok(())
    } else {
        Err(RuntimeError::new(format!(
            "{context} expects a bool but found {}",
            describe_type(ty)
        )))
    }
}

fn ensure_comparable(
    left: &Type,
    right: &Type,
    op_name: &str,
) -> Result<(), RuntimeError> {
    if is_dyn_like(left) || is_dyn_like(right) {
        return Ok(());
    }
    let comparable = (is_numeric_type(left) && is_numeric_type(right))
        || matches!(left, Type::String) && matches!(right, Type::String)
        || matches!(left, Type::Bytes) && matches!(right, Type::Bytes);
    if comparable {
        Ok(())
    } else {
        Err(RuntimeError::new(format!(
            "Operator '{op_name}' is not defined for types {} and {}",
            describe_type(left),
            describe_type(right)
        )))
    }
}

fn ensure_index_operand(ty: &Type, context: &str) -> Result<(), RuntimeError> {
    if matches!(ty, Type::Int | Type::Uint) || is_dyn_like(ty) {
        Ok(())
    } else {
        Err(RuntimeError::new(format!(
            "{context} index expects an integer but found {}",
            describe_type(ty)
        )))
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum NumericKind {
    Int,
    Uint,
    Double,
}

#[derive(Clone, Copy)]
enum NumericBinaryOp {
    Add,
    Subtract,
    Multiply,
    Divide,
    Modulo,
}

impl NumericBinaryOp {
    fn description(self) -> &'static str {
        match self {
            NumericBinaryOp::Add => "addition",
            NumericBinaryOp::Subtract => "subtraction",
            NumericBinaryOp::Multiply => "multiplication",
            NumericBinaryOp::Divide => "division",
            NumericBinaryOp::Modulo => "modulo",
        }
    }
}

fn numeric_kind(ty: &Type, context: &str) -> Result<NumericKind, RuntimeError> {
    match ty {
        Type::Int => Ok(NumericKind::Int),
        Type::Uint => Ok(NumericKind::Uint),
        Type::Double => Ok(NumericKind::Double),
        _ => Err(RuntimeError::new(format!(
            "{context} expects numeric values but found {}",
            describe_type(ty)
        ))),
    }
}

fn numeric_unary_result(
    operand: &Type,
    context: &str,
) -> Result<Type, RuntimeError> {
    if is_dyn_like(operand) {
        return Ok(Type::Dyn);
    }
    match operand {
        Type::Int => Ok(Type::Int),
        Type::Double => Ok(Type::Double),
        _ => Err(RuntimeError::new(format!(
            "{context} expects int or double but found {}",
            describe_type(operand)
        ))),
    }
}

fn numeric_binary_result(
    left: &Type,
    right: &Type,
    op: NumericBinaryOp,
) -> Result<Type, RuntimeError> {
    if is_dyn_like(left) || is_dyn_like(right) {
        return Ok(Type::Dyn);
    }
    let context = op.description();
    let left_kind = numeric_kind(left, context)?;
    let right_kind = numeric_kind(right, context)?;
    match op {
        NumericBinaryOp::Add
        | NumericBinaryOp::Subtract
        | NumericBinaryOp::Multiply => {
            if left_kind == right_kind {
                Ok(type_from_numeric_kind(left_kind))
            } else {
                Ok(Type::Double)
            }
        }
        NumericBinaryOp::Divide => Ok(Type::Double),
        NumericBinaryOp::Modulo => match (left_kind, right_kind) {
            (NumericKind::Int, NumericKind::Int) => Ok(Type::Int),
            (NumericKind::Uint, NumericKind::Uint) => Ok(Type::Uint),
            _ => Err(RuntimeError::new(
                "Modulo operator is only defined for matching integral types",
            )),
        },
    }
}

fn type_from_numeric_kind(kind: NumericKind) -> Type {
    match kind {
        NumericKind::Int => Type::Int,
        NumericKind::Uint => Type::Uint,
        NumericKind::Double => Type::Double,
    }
}

fn is_numeric_type(ty: &Type) -> bool {
    matches!(ty, Type::Int | Type::Uint | Type::Double)
}

fn describe_type(ty: &Type) -> String {
    match ty {
        Type::Dyn => "dyn".into(),
        Type::Any => "any".into(),
        Type::Null => "null".into(),
        Type::Type => "type".into(),
        Type::Bool => "bool".into(),
        Type::Int => "int".into(),
        Type::Uint => "uint".into(),
        Type::Double => "double".into(),
        Type::String => "string".into(),
        Type::Bytes => "bytes".into(),
        Type::Timestamp => "timestamp".into(),
        Type::Duration => "duration".into(),
        Type::List(inner) => format!("list<{}>", describe_type(inner)),
        Type::Map(key, value) => {
            format!("map<{}, {}>", describe_type(key), describe_type(value))
        }
        Type::Struct(name) => format!("struct {}", name.as_str()),
        Type::Enum(name) => format!("enum {}", name.as_str()),
        Type::TypeParam(name) => format!("type_param {name}"),
    }
}

fn unify_types(left: Type, right: Type) -> Result<Type, RuntimeError> {
    if is_dyn_like(&left) {
        return Ok(right);
    }
    if is_dyn_like(&right) {
        return Ok(left);
    }
    if left == right {
        return Ok(left);
    }
    if let Some(numeric) = merge_numeric_types(&left, &right) {
        return Ok(numeric);
    }
    match (&left, &right) {
        (Type::List(a), Type::List(b)) => {
            let merged = unify_types((**a).clone(), (**b).clone())?;
            Ok(Type::list(merged))
        }
        (Type::Map(ka, va), Type::Map(kb, vb)) => {
            let key = unify_types((**ka).clone(), (**kb).clone())?;
            let value = unify_types((**va).clone(), (**vb).clone())?;
            Ok(Type::map(key, value))
        }
        _ => Err(RuntimeError::new(format!(
            "Type mismatch between {} and {}",
            describe_type(&left),
            describe_type(&right)
        ))),
    }
}

fn merge_numeric_types(left: &Type, right: &Type) -> Option<Type> {
    match (left, right) {
        (Type::Int, Type::Int) => Some(Type::Int),
        (Type::Uint, Type::Uint) => Some(Type::Uint),
        (Type::Double, Type::Double)
        | (Type::Int, Type::Double)
        | (Type::Double, Type::Int)
        | (Type::Uint, Type::Double)
        | (Type::Double, Type::Uint)
        | (Type::Uint, Type::Int)
        | (Type::Int, Type::Uint) => Some(Type::Double),
        _ => None,
    }
}

fn format_type_list(types: &[Type]) -> String {
    types
        .iter()
        .map(describe_type)
        .collect::<Vec<_>>()
        .join(", ")
}

fn make_binary(
    op: BinaryOp,
    ty: Type,
    left: TypedExpr,
    right: TypedExpr,
) -> TypedExpr {
    TypedExpr::new(
        ty,
        ExprKind::Binary {
            op,
            left: Box::new(left),
            right: Box::new(right),
        },
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::Env;
    use crate::types::{
        FieldDecl, FunctionDecl, IdentDecl, NamedType, OverloadDecl, StructType,
    };

    fn declared_user_env() -> Env {
        const USER_TYPE: &str = "example.User";
        let mut user = StructType::new(USER_TYPE);
        user.add_field("name", FieldDecl::new(Type::String))
            .unwrap();
        user.add_field("roles", FieldDecl::new(Type::list(Type::String)))
            .unwrap();

        let mut builder = Env::builder();
        builder.add_type(NamedType::Struct(user.clone())).unwrap();
        builder
            .add_ident(IdentDecl::new(
                "user",
                Type::struct_type(user.name.clone()),
            ))
            .unwrap();

        let mut func = FunctionDecl::new("has_role");
        func.add_overload(
            OverloadDecl::new(
                "user_has_role_string",
                vec![Type::String],
                Type::Bool,
            )
            .with_receiver(Type::struct_type(user.name.clone())),
        )
        .unwrap();
        builder.add_function(func).unwrap();
        builder.build()
    }

    #[test]
    fn infers_identifier_types() {
        let mut builder = Env::builder();
        builder.add_ident(IdentDecl::new("x", Type::Int)).unwrap();
        let env = builder.build();
        let hir_expr = HirExpr::Atom(HirAtom::Ident("x".to_string()));
        let expr = type_check(&env, &hir_expr).unwrap();
        assert_eq!(expr.ty, Type::Int);
    }

    #[test]
    fn infers_method_call_type() {
        let env = declared_user_env();
        let hir_expr =
            crate::hir::lower_source("user.has_role('admin')").expect("lower");
        let typed = type_check(&env, &hir_expr).expect("type check");
        assert_eq!(typed.ty, Type::Bool);
    }

    #[test]
    fn reports_unknown_identifier() {
        let env = Env::builder().build();
        let hir_expr = crate::hir::lower_source("missing + 1").expect("lower");
        let err = type_check(&env, &hir_expr).expect_err("type error");
        assert!(err.to_string().contains("Identifier 'missing'"));
    }

    #[test]
    fn typed_expr_serialization() {
        let expr = TypedExpr::new(
            Type::Int,
            ExprKind::Binary {
                op: BinaryOp::Add,
                left: Box::new(TypedExpr::new(
                    Type::Int,
                    ExprKind::Literal(LiteralValue::Int(1)),
                )),
                right: Box::new(TypedExpr::new(
                    Type::Int,
                    ExprKind::Literal(LiteralValue::Int(2)),
                )),
            },
        );
        let serialized =
            serde_json::to_string(&expr).expect("serialize typed expr");
        let deserialized: TypedExpr =
            serde_json::from_str(&serialized).expect("deserialize typed expr");
        assert_eq!(expr, deserialized);
    }
}
