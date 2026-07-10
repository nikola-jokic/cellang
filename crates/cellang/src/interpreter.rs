//! Evaluation layer: Runtime execution of typed expressions.
//!
//! This module forms the **fourth and final stage** of the CEL pipeline:
//! CST (`crate::syntax`) → HIR (`crate::hir`) → Type Check (`crate::ast`) → Eval (this module)
//!
//! The evaluator consumes fully typed `TypedExpr` graphs produced by the type checker and
//! executes them within a runtime context, producing `Value` results. The runtime context
//! provides variable bindings, native function implementations, and environment for evaluation.
//!
//! **Module boundary**: This module is internal to the parser pipeline. External code should use
//! the public API facade at `crate::parser::eval` or `crate::parser::eval_ast` rather than
//! importing directly from this module.

use crate::error::RuntimeError;
use crate::hir::expr::{
    Atom as HirAtom, BinaryOp as HirBinaryOp, Expr as HirExpr,
    UnaryOp as HirUnaryOp,
};
use crate::macros::{self, ComprehensionKind, MacroInvocation};
use crate::runtime::{CallContext, Runtime};
use crate::value::{Key, ListValue, MapValue, TryFromValue, Value, ValueError};
use std::cmp::Ordering;

/// Evaluates the given source string in the context of the provided runtime,
/// returning the resulting value.
pub fn eval(runtime: &Runtime, source: &str) -> Result<Value, RuntimeError> {
    let hir_expr = crate::hir::lower_source(source)?;
    eval_ast(runtime, &hir_expr)
}

/// Evaluates the given HIR expression in the context of the provided runtime,
/// returning the resulting value.
pub fn eval_ast(
    runtime: &Runtime,
    expr: &HirExpr,
) -> Result<Value, RuntimeError> {
    let mut ctx = EvalContext::new(runtime);
    eval_expr(&mut ctx, expr)
}

struct EvalContext<'a> {
    runtime: &'a Runtime,
    locals: Vec<(String, Value)>,
}

impl<'a> EvalContext<'a> {
    fn new(runtime: &'a Runtime) -> Self {
        Self {
            runtime,
            locals: Vec::new(),
        }
    }

    fn runtime(&self) -> &'a Runtime {
        self.runtime
    }

    fn resolve_identifier(&self, name: &str) -> Option<Value> {
        if let Some((_, value)) = self
            .locals
            .iter()
            .rev()
            .find(|(binding, _)| binding == name)
        {
            return Some(value.clone());
        }
        self.runtime.resolve_identifier(name)
    }

    fn with_local<F, R>(
        &mut self,
        name: &str,
        value: Value,
        f: F,
    ) -> Result<R, RuntimeError>
    where
        F: FnOnce(&mut EvalContext<'a>) -> Result<R, RuntimeError>,
    {
        self.locals.push((name.to_string(), value));
        let result = f(self);
        self.locals.pop();
        result
    }
}

fn eval_expr(
    ctx: &mut EvalContext<'_>,
    expr: &HirExpr,
) -> Result<Value, RuntimeError> {
    match expr {
        HirExpr::Atom(atom) => eval_atom(ctx, atom),
        HirExpr::Unary { op, expr: inner } => eval_unary(ctx, *op, inner),
        HirExpr::Binary { op, lhs, rhs } => eval_binary(ctx, *op, lhs, rhs),
        HirExpr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => eval_ternary(ctx, cond, then_expr, else_expr),
        HirExpr::Call {
            func,
            args,
            is_method,
        } => eval_call(ctx, func, args, *is_method),
        HirExpr::Field { target, field } => eval_field(ctx, target, field),
        HirExpr::Index { target, index } => eval_index_expr(ctx, target, index),
        HirExpr::List(elements) => eval_list(ctx, elements),
        HirExpr::Map(entries) => eval_map(ctx, entries),
        HirExpr::Group(inner) | HirExpr::Dyn(inner) => eval_expr(ctx, inner),
    }
}

fn eval_atom(
    ctx: &mut EvalContext<'_>,
    atom: &HirAtom,
) -> Result<Value, RuntimeError> {
    Ok(match atom {
        HirAtom::Bool(value) => Value::Bool(*value),
        HirAtom::Int(value) => Value::Int(*value),
        HirAtom::Uint(value) => Value::Uint(*value),
        HirAtom::Double(value) => Value::Double(*value),
        HirAtom::String(value) => Value::String(value.clone()),
        HirAtom::Bytes(value) => Value::Bytes(value.clone()),
        HirAtom::Null => Value::Null,
        HirAtom::Ident(name) => ctx
            .resolve_identifier(name)
            .ok_or_else(|| RuntimeError::missing_identifier(name))?,
    })
}

fn eval_unary(
    ctx: &mut EvalContext<'_>,
    op: HirUnaryOp,
    expr: &HirExpr,
) -> Result<Value, RuntimeError> {
    let value = eval_expr(ctx, expr)?;
    match op {
        HirUnaryOp::Not => {
            let flag = <bool as TryFromValue>::try_from_value(&value).map_err(
                |err| RuntimeError::with_source("expected bool", err),
            )?;
            Ok(Value::Bool(!flag))
        }
        HirUnaryOp::Neg => negate_value(&value),
    }
}

fn eval_binary(
    ctx: &mut EvalContext<'_>,
    op: HirBinaryOp,
    lhs: &HirExpr,
    rhs: &HirExpr,
) -> Result<Value, RuntimeError> {
    match op {
        HirBinaryOp::And => {
            let left = eval_expr(ctx, lhs)?;
            let left_flag = <bool as TryFromValue>::try_from_value(&left)
                .map_err(|err| {
                    RuntimeError::with_source("expected bool", err)
                })?;
            if !left_flag {
                return Ok(Value::Bool(false));
            }
            let right = eval_expr(ctx, rhs)?;
            let right_flag = <bool as TryFromValue>::try_from_value(&right)
                .map_err(|err| {
                    RuntimeError::with_source("expected bool", err)
                })?;
            Ok(Value::Bool(right_flag))
        }
        HirBinaryOp::Or => {
            let left = eval_expr(ctx, lhs)?;
            let left_flag = <bool as TryFromValue>::try_from_value(&left)
                .map_err(|err| {
                    RuntimeError::with_source("expected bool", err)
                })?;
            if left_flag {
                return Ok(Value::Bool(true));
            }
            let right = eval_expr(ctx, rhs)?;
            let right_flag = <bool as TryFromValue>::try_from_value(&right)
                .map_err(|err| {
                    RuntimeError::with_source("expected bool", err)
                })?;
            Ok(Value::Bool(right_flag))
        }
        _ => {
            let left = eval_expr(ctx, lhs)?;
            let right = eval_expr(ctx, rhs)?;
            match op {
                HirBinaryOp::Add => add_values(&left, &right),
                HirBinaryOp::Sub => subtract_values(&left, &right),
                HirBinaryOp::Mul => multiply_values(&left, &right),
                HirBinaryOp::Div => divide_values(&left, &right),
                HirBinaryOp::Mod => modulo_values(&left, &right),
                HirBinaryOp::Eq => Ok(Value::Bool(left == right)),
                HirBinaryOp::Ne => Ok(Value::Bool(left != right)),
                HirBinaryOp::Lt => {
                    let ordering = compare_values(&left, &right)?;
                    Ok(Value::Bool(ordering == Ordering::Less))
                }
                HirBinaryOp::Le => {
                    let ordering = compare_values(&left, &right)?;
                    Ok(Value::Bool(ordering != Ordering::Greater))
                }
                HirBinaryOp::Gt => {
                    let ordering = compare_values(&left, &right)?;
                    Ok(Value::Bool(ordering == Ordering::Greater))
                }
                HirBinaryOp::Ge => {
                    let ordering = compare_values(&left, &right)?;
                    Ok(Value::Bool(ordering != Ordering::Less))
                }
                HirBinaryOp::In => eval_in_operator(&left, &right),
                HirBinaryOp::And | HirBinaryOp::Or => unreachable!(),
            }
        }
    }
}

fn eval_ternary(
    ctx: &mut EvalContext<'_>,
    cond: &HirExpr,
    then_expr: &HirExpr,
    else_expr: &HirExpr,
) -> Result<Value, RuntimeError> {
    let condition = eval_expr(ctx, cond)?;
    let flag = <bool as TryFromValue>::try_from_value(&condition)
        .map_err(|err| RuntimeError::with_source("expected bool", err))?;
    if flag {
        eval_expr(ctx, then_expr)
    } else {
        eval_expr(ctx, else_expr)
    }
}

fn eval_list(
    ctx: &mut EvalContext<'_>,
    elements: &[HirExpr],
) -> Result<Value, RuntimeError> {
    let mut list = ListValue::new();
    for expr in elements {
        list.push(eval_expr(ctx, expr)?);
    }
    Ok(Value::List(list))
}

fn eval_map(
    ctx: &mut EvalContext<'_>,
    entries: &[(HirExpr, HirExpr)],
) -> Result<Value, RuntimeError> {
    let mut map = MapValue::new();
    for (key_expr, value_expr) in entries {
        let key_value = eval_expr(ctx, key_expr)?;
        let key = Key::try_from(&key_value).map_err(|err| {
            RuntimeError::with_source(
                "cannot use non-primitive value as map key",
                err,
            )
        })?;
        let value = eval_expr(ctx, value_expr)?;
        map.insert(key, value);
    }
    Ok(Value::Map(map))
}

fn eval_call(
    ctx: &mut EvalContext<'_>,
    func: &HirExpr,
    args: &[HirExpr],
    is_method: bool,
) -> Result<Value, RuntimeError> {
    let name = resolve_hir_function_name(func).ok_or_else(|| {
        eprintln!("DEBUG: Failed to resolve function name from: {:#?}", func);
        RuntimeError::new("function calls must reference an identifier")
    })?;
    if let Some(invocation) = macros::detect_macro_call(
        ctx.runtime().macros(),
        func,
        args,
        is_method,
    )? {
        return eval_macro(ctx, invocation);
    }
    let handler = ctx.runtime().lookup_function(&name).ok_or_else(|| {
        RuntimeError::new(format!("Function '{name}' is not registered"))
    })?;
    let mut evaluated = Vec::with_capacity(args.len());
    for expr in args {
        evaluated.push(eval_expr(ctx, expr)?);
    }
    let context = CallContext::new(ctx.runtime(), &evaluated);
    handler(&context)
}

fn resolve_hir_function_name(expr: &HirExpr) -> Option<String> {
    match expr {
        HirExpr::Atom(HirAtom::Ident(name)) => Some(name.clone()),
        HirExpr::Field { target, field } => {
            let left = resolve_hir_function_name(target)?;
            Some(format!("{}.{}", left, field))
        }
        HirExpr::Group(inner) => resolve_hir_function_name(inner),
        _ => None,
    }
}

fn eval_macro(
    ctx: &mut EvalContext<'_>,
    invocation: MacroInvocation,
) -> Result<Value, RuntimeError> {
    match invocation {
        MacroInvocation::Has { target, field } => {
            eval_has_macro(ctx, &target, &field)
        }
        MacroInvocation::Comprehension {
            kind,
            range,
            var,
            predicate,
            transform,
        } => match kind {
            ComprehensionKind::All => {
                let pred = predicate.as_ref().expect("predicate validated");
                eval_all_macro(ctx, &range, &var, pred)
            }
            ComprehensionKind::Exists => {
                let pred = predicate.as_ref().expect("predicate validated");
                eval_exists_macro(ctx, &range, &var, pred)
            }
            ComprehensionKind::ExistsOne => {
                let pred = predicate.as_ref().expect("predicate validated");
                eval_exists_one_macro(ctx, &range, &var, pred)
            }
            ComprehensionKind::Map => {
                let trans = transform.as_ref().expect("transform validated");
                eval_map_macro(ctx, &range, &var, predicate.as_ref(), trans)
            }
            ComprehensionKind::Filter => {
                let pred = predicate.as_ref().expect("predicate validated");
                eval_filter_macro(ctx, &range, &var, pred)
            }
        },
    }
}

fn eval_has_macro(
    ctx: &mut EvalContext<'_>,
    target_expr: &HirExpr,
    field: &str,
) -> Result<Value, RuntimeError> {
    let target = eval_expr(ctx, target_expr)?;
    let result = match target {
        Value::Struct(strct) => strct.get(field).is_some(),
        Value::Map(map) => map.contains_key(&Key::from(field)),
        Value::Null => {
            return Err(RuntimeError::new(
                "has() macro cannot operate on null values",
            ));
        }
        other => {
            return Err(RuntimeError::new(format!(
                "has() macro is not supported for values of kind {}",
                other.kind()
            )));
        }
    };
    Ok(Value::Bool(result))
}

fn eval_all_macro(
    ctx: &mut EvalContext<'_>,
    range_expr: &HirExpr,
    var: &str,
    predicate: &HirExpr,
) -> Result<Value, RuntimeError> {
    let range = eval_expr(ctx, range_expr)?;
    let outcome = match range {
        Value::List(list) => {
            eval_all_over_iter(ctx, list.iter().cloned(), var, predicate)?
        }
        Value::Map(map) => eval_all_over_iter(
            ctx,
            map.iter().map(|(key, _)| Value::from(key)),
            var,
            predicate,
        )?,
        other => return Err(invalid_range("all", &other)),
    };
    Ok(Value::Bool(outcome))
}

fn eval_exists_macro(
    ctx: &mut EvalContext<'_>,
    range_expr: &HirExpr,
    var: &str,
    predicate: &HirExpr,
) -> Result<Value, RuntimeError> {
    let range = eval_expr(ctx, range_expr)?;
    let outcome = match range {
        Value::List(list) => {
            eval_exists_over_iter(ctx, list.iter().cloned(), var, predicate)?
        }
        Value::Map(map) => eval_exists_over_iter(
            ctx,
            map.iter().map(|(key, _)| Value::from(key)),
            var,
            predicate,
        )?,
        other => return Err(invalid_range("exists", &other)),
    };
    Ok(Value::Bool(outcome))
}

fn eval_exists_one_macro(
    ctx: &mut EvalContext<'_>,
    range_expr: &HirExpr,
    var: &str,
    predicate: &HirExpr,
) -> Result<Value, RuntimeError> {
    let range = eval_expr(ctx, range_expr)?;
    let matches = match range {
        Value::List(list) => eval_exists_one_over_iter(
            ctx,
            list.iter().cloned(),
            var,
            predicate,
        )?,
        Value::Map(map) => eval_exists_one_over_iter(
            ctx,
            map.iter().map(|(key, _)| Value::from(key)),
            var,
            predicate,
        )?,
        other => return Err(invalid_range("exists_one", &other)),
    };
    Ok(Value::Bool(matches == 1))
}

fn eval_map_macro(
    ctx: &mut EvalContext<'_>,
    range_expr: &HirExpr,
    var: &str,
    predicate: Option<&HirExpr>,
    transform: &HirExpr,
) -> Result<Value, RuntimeError> {
    let range = eval_expr(ctx, range_expr)?;
    match range {
        Value::List(list) => eval_map_over_iter(
            ctx,
            list.iter().cloned(),
            var,
            predicate,
            transform,
        ),
        Value::Map(map) => eval_map_over_iter(
            ctx,
            map.iter().map(|(key, _)| Value::from(key)),
            var,
            predicate,
            transform,
        ),
        other => Err(invalid_range("map", &other)),
    }
}

fn eval_filter_macro(
    ctx: &mut EvalContext<'_>,
    range_expr: &HirExpr,
    var: &str,
    predicate: &HirExpr,
) -> Result<Value, RuntimeError> {
    let range = eval_expr(ctx, range_expr)?;
    match range {
        Value::List(list) => {
            eval_filter_over_iter(ctx, list.iter().cloned(), var, predicate)
        }
        Value::Map(map) => eval_filter_over_iter(
            ctx,
            map.iter().map(|(key, _)| Value::from(key)),
            var,
            predicate,
        ),
        other => Err(invalid_range("filter", &other)),
    }
}

fn eval_all_over_iter<I>(
    ctx: &mut EvalContext<'_>,
    iter: I,
    var: &str,
    predicate: &HirExpr,
) -> Result<bool, RuntimeError>
where
    I: IntoIterator<Item = Value>,
{
    for value in iter {
        let flag = ctx.with_local(var, value, |ctx| {
            let evaluated = eval_expr(ctx, predicate)?;
            bool_from_value(evaluated)
        })?;
        if !flag {
            return Ok(false);
        }
    }
    Ok(true)
}

fn eval_exists_over_iter<I>(
    ctx: &mut EvalContext<'_>,
    iter: I,
    var: &str,
    predicate: &HirExpr,
) -> Result<bool, RuntimeError>
where
    I: IntoIterator<Item = Value>,
{
    for value in iter {
        let flag = ctx.with_local(var, value, |ctx| {
            let evaluated = eval_expr(ctx, predicate)?;
            bool_from_value(evaluated)
        })?;
        if flag {
            return Ok(true);
        }
    }
    Ok(false)
}

fn eval_exists_one_over_iter<I>(
    ctx: &mut EvalContext<'_>,
    iter: I,
    var: &str,
    predicate: &HirExpr,
) -> Result<usize, RuntimeError>
where
    I: IntoIterator<Item = Value>,
{
    let mut matches = 0usize;
    for value in iter {
        let flag = ctx.with_local(var, value, |ctx| {
            let evaluated = eval_expr(ctx, predicate)?;
            bool_from_value(evaluated)
        })?;
        if flag {
            matches += 1;
        }
    }
    Ok(matches)
}

fn eval_map_over_iter<I>(
    ctx: &mut EvalContext<'_>,
    iter: I,
    var: &str,
    predicate: Option<&HirExpr>,
    transform: &HirExpr,
) -> Result<Value, RuntimeError>
where
    I: IntoIterator<Item = Value>,
{
    let mut result = ListValue::new();
    for value in iter {
        let passes = if let Some(pred) = predicate {
            ctx.with_local(var, value.clone(), |ctx| {
                let evaluated = eval_expr(ctx, pred)?;
                bool_from_value(evaluated)
            })?
        } else {
            true
        };
        if passes {
            let mapped =
                ctx.with_local(var, value, |ctx| eval_expr(ctx, transform))?;
            result.push(mapped);
        }
    }
    Ok(Value::List(result))
}

fn eval_filter_over_iter<I>(
    ctx: &mut EvalContext<'_>,
    iter: I,
    var: &str,
    predicate: &HirExpr,
) -> Result<Value, RuntimeError>
where
    I: IntoIterator<Item = Value>,
{
    let mut result = ListValue::new();
    for value in iter {
        let keep = ctx.with_local(var, value.clone(), |ctx| {
            let evaluated = eval_expr(ctx, predicate)?;
            bool_from_value(evaluated)
        })?;
        if keep {
            result.push(value);
        }
    }
    Ok(Value::List(result))
}

fn bool_from_value(value: Value) -> Result<bool, RuntimeError> {
    <bool as TryFromValue>::try_from_value(&value)
        .map_err(|err| RuntimeError::with_source("expected bool", err))
}

fn invalid_range(name: &str, value: &Value) -> RuntimeError {
    RuntimeError::new(format!(
        "Macro '{name}' expects a list or map but found {}",
        value.kind()
    ))
}

fn eval_field(
    ctx: &mut EvalContext<'_>,
    target_expr: &HirExpr,
    field: &str,
) -> Result<Value, RuntimeError> {
    let target = eval_expr(ctx, target_expr)?;
    match target {
        Value::Struct(strct) => strct.get(field).cloned().ok_or_else(|| {
            RuntimeError::new(format!(
                "Struct '{}' does not contain field '{field}'",
                strct.type_name
            ))
        }),
        Value::Map(map) => map.get_str(field).cloned().ok_or_else(|| {
            RuntimeError::new(format!(
                "Map value does not contain key '{field}'"
            ))
        }),
        Value::Null => Err(RuntimeError::new("Cannot access fields on null")),
        other => Err(RuntimeError::new(format!(
            "Field access is not supported on values of kind {}",
            other.kind()
        ))),
    }
}

fn eval_in_operator(
    needle: &Value,
    haystack: &Value,
) -> Result<Value, RuntimeError> {
    let result = match haystack {
        Value::List(list) => list.iter().any(|value| value == needle),
        Value::Map(map) => {
            let key = Key::try_from(needle).map_err(RuntimeError::from)?;
            map.contains_key(&key)
        }
        Value::String(text) => {
            let query = <String as TryFromValue>::try_from_value(needle)
                .map_err(|err| {
                    RuntimeError::with_source("expected string", err)
                })?;
            text.contains(&query)
        }
        Value::Bytes(bytes) => {
            let query = <Vec<u8> as TryFromValue>::try_from_value(needle)
                .map_err(|err| {
                    RuntimeError::with_source("expected bytes", err)
                })?;
            bytes
                .windows(query.len())
                .any(|window| window == query.as_slice())
        }
        _ => {
            return Err(RuntimeError::new(format!(
                "Operator 'in' is not supported for values of kind {}",
                haystack.kind()
            )));
        }
    };
    Ok(Value::Bool(result))
}

fn eval_index_expr(
    ctx: &mut EvalContext<'_>,
    target_expr: &HirExpr,
    index_expr: &HirExpr,
) -> Result<Value, RuntimeError> {
    let target = eval_expr(ctx, target_expr)?;
    let index = eval_expr(ctx, index_expr)?;
    eval_index(&target, &index)
}

fn eval_index(target: &Value, index: &Value) -> Result<Value, RuntimeError> {
    match target {
        Value::List(list) => {
            let idx = expect_index(index, list.len())?;
            list.get(idx)
                .cloned()
                .ok_or_else(|| RuntimeError::new("list index out of bounds"))
        }
        Value::String(text) => {
            let idx = expect_index(index, text.chars().count())?;
            let ch = text.chars().nth(idx).ok_or_else(|| {
                RuntimeError::new("string index out of bounds")
            })?;
            Ok(Value::String(ch.to_string()))
        }
        Value::Bytes(bytes) => {
            let idx = expect_index(index, bytes.len())?;
            Ok(Value::Uint(bytes[idx] as u64))
        }
        Value::Map(map) => {
            let key = Key::try_from(index).map_err(RuntimeError::from)?;
            map.get_by_key(&key)
                .cloned()
                .ok_or_else(|| RuntimeError::new("map key does not exist"))
        }
        Value::Struct(strct) => {
            let field = <String as TryFromValue>::try_from_value(index)
                .map_err(|err| {
                    RuntimeError::with_source(
                        "struct index expects field name",
                        err,
                    )
                })?;
            strct.get(&field).cloned().ok_or_else(|| {
                RuntimeError::new(format!(
                    "Struct '{}' does not contain field '{field}'",
                    strct.type_name
                ))
            })
        }
        Value::Null => Err(RuntimeError::new("Cannot index null")),
        other => Err(RuntimeError::new(format!(
            "Index operator is not supported for values of kind {}",
            other.kind()
        ))),
    }
}

fn compare_values(
    left: &Value,
    right: &Value,
) -> Result<Ordering, RuntimeError> {
    match (left, right) {
        (Value::String(a), Value::String(b)) => Ok(a.cmp(b)),
        (Value::Bytes(a), Value::Bytes(b)) => Ok(a.cmp(b)),
        _ => {
            let left = Number::from_value(left)?;
            let right = Number::from_value(right)?;
            compare_numeric(left, right)
        }
    }
}

fn add_values(left: &Value, right: &Value) -> Result<Value, RuntimeError> {
    match (left, right) {
        (Value::String(a), Value::String(b)) => {
            let mut result = String::with_capacity(a.len() + b.len());
            result.push_str(a);
            result.push_str(b);
            Ok(Value::String(result))
        }
        (Value::Bytes(a), Value::Bytes(b)) => {
            let mut result = a.clone();
            result.extend_from_slice(b);
            Ok(Value::Bytes(result))
        }
        (Value::List(a), Value::List(b)) => {
            let mut merged = a.clone().into_vec();
            merged.extend(b.clone().into_vec());
            Ok(Value::List(ListValue::from(merged)))
        }
        _ => {
            let left = Number::from_value(left)?;
            let right = Number::from_value(right)?;
            left.add(right)
        }
    }
}

fn subtract_values(left: &Value, right: &Value) -> Result<Value, RuntimeError> {
    let left = Number::from_value(left)?;
    let right = Number::from_value(right)?;
    left.sub(right)
}

fn multiply_values(left: &Value, right: &Value) -> Result<Value, RuntimeError> {
    let left = Number::from_value(left)?;
    let right = Number::from_value(right)?;
    left.mul(right)
}

fn divide_values(left: &Value, right: &Value) -> Result<Value, RuntimeError> {
    let left = Number::from_value(left)?;
    let right = Number::from_value(right)?;
    left.div(right)
}

fn modulo_values(left: &Value, right: &Value) -> Result<Value, RuntimeError> {
    let left = Number::from_value(left)?;
    let right = Number::from_value(right)?;
    left.rem(right)
}

fn negate_value(value: &Value) -> Result<Value, RuntimeError> {
    match value {
        Value::Int(v) => Ok(Value::Int(-v)),
        Value::Double(v) => Ok(Value::Double(-v)),
        _ => Err(RuntimeError::new("Unary minus expects an int or double")),
    }
}

fn expect_index(index: &Value, len: usize) -> Result<usize, RuntimeError> {
    let position = match index {
        Value::Int(value) if *value >= 0 => *value as usize,
        Value::Uint(value) => *value as usize,
        _ => {
            return Err(RuntimeError::new(
                "index operator expects a non-negative integer",
            ));
        }
    };

    if position >= len {
        return Err(RuntimeError::from(ValueError::IndexOutOfBounds {
            index: position,
            len,
        }));
    }
    Ok(position)
}

fn compare_numeric(
    left: Number,
    right: Number,
) -> Result<Ordering, RuntimeError> {
    match (left, right) {
        (Number::Int(a), Number::Int(b)) => Ok(a.cmp(&b)),
        (Number::Uint(a), Number::Uint(b)) => Ok(a.cmp(&b)),
        (Number::Double(a), Number::Double(b)) => {
            a.partial_cmp(&b).ok_or_else(|| {
                RuntimeError::new("comparison with NaN is undefined")
            })
        }
        (left, right) => {
            left.as_f64().partial_cmp(&right.as_f64()).ok_or_else(|| {
                RuntimeError::new("comparison with NaN is undefined")
            })
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum Number {
    Int(i64),
    Uint(u64),
    Double(f64),
}

impl Number {
    fn from_value(value: &Value) -> Result<Self, RuntimeError> {
        match value {
            Value::Int(v) => Ok(Number::Int(*v)),
            Value::Uint(v) => Ok(Number::Uint(*v)),
            Value::Double(v) => Ok(Number::Double(*v)),
            _ => Err(RuntimeError::new(format!(
                "Expected numeric value but found {}",
                value.kind()
            ))),
        }
    }

    fn add(self, other: Number) -> Result<Value, RuntimeError> {
        match (self, other) {
            (Number::Int(a), Number::Int(b)) => a
                .checked_add(b)
                .map(Value::Int)
                .ok_or_else(|| RuntimeError::new("addition overflowed")),
            (Number::Uint(a), Number::Uint(b)) => a
                .checked_add(b)
                .map(Value::Uint)
                .ok_or_else(|| RuntimeError::new("addition overflowed")),
            (Number::Double(a), Number::Double(b)) => Ok(Value::Double(a + b)),
            (left, right) => Ok(Value::Double(left.as_f64() + right.as_f64())),
        }
    }

    fn sub(self, other: Number) -> Result<Value, RuntimeError> {
        match (self, other) {
            (Number::Int(a), Number::Int(b)) => a
                .checked_sub(b)
                .map(Value::Int)
                .ok_or_else(|| RuntimeError::new("subtraction overflowed")),
            (Number::Uint(a), Number::Uint(b)) => a
                .checked_sub(b)
                .map(Value::Uint)
                .ok_or_else(|| RuntimeError::new("subtraction overflowed")),
            (Number::Double(a), Number::Double(b)) => Ok(Value::Double(a - b)),
            (left, right) => Ok(Value::Double(left.as_f64() - right.as_f64())),
        }
    }

    fn mul(self, other: Number) -> Result<Value, RuntimeError> {
        match (self, other) {
            (Number::Int(a), Number::Int(b)) => a
                .checked_mul(b)
                .map(Value::Int)
                .ok_or_else(|| RuntimeError::new("multiplication overflowed")),
            (Number::Uint(a), Number::Uint(b)) => a
                .checked_mul(b)
                .map(Value::Uint)
                .ok_or_else(|| RuntimeError::new("multiplication overflowed")),
            (Number::Double(a), Number::Double(b)) => Ok(Value::Double(a * b)),
            (left, right) => Ok(Value::Double(left.as_f64() * right.as_f64())),
        }
    }

    fn div(self, other: Number) -> Result<Value, RuntimeError> {
        let divisor = other.as_f64();
        if divisor == 0.0 {
            return Err(RuntimeError::new("division by zero"));
        }
        Ok(Value::Double(self.as_f64() / divisor))
    }

    fn rem(self, other: Number) -> Result<Value, RuntimeError> {
        match (self, other) {
            (Number::Int(a), Number::Int(b)) => {
                if b == 0 {
                    Err(RuntimeError::new("modulo by zero"))
                } else {
                    Ok(Value::Int(a % b))
                }
            }
            (Number::Uint(a), Number::Uint(b)) => {
                if b == 0 {
                    Err(RuntimeError::new("modulo by zero"))
                } else {
                    Ok(Value::Uint(a % b))
                }
            }
            _ => Err(RuntimeError::new(
                "Modulo operator is only defined for integral values",
            )),
        }
    }

    fn as_f64(self) -> f64 {
        match self {
            Number::Int(value) => value as f64,
            Number::Uint(value) => value as f64,
            Number::Double(value) => value,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::runtime::Runtime;
    use crate::value::{IntoValue, ListValue, MapValue, StructValue, Value};

    #[test]
    fn evaluates_arithmetic_with_variables() {
        let mut builder = Runtime::builder();
        builder
            .set_variable("x", Value::Int(6))
            .expect("variable to set");
        let runtime = builder.build();
        let result = eval(&runtime, "x * 2 + 1").expect("expression evaluates");
        assert_eq!(result, Value::Int(13));
    }

    #[test]
    fn struct_field_access_returns_value() {
        let runtime = runtime_with_user();
        let value = eval(&runtime, "user.name").expect("field access succeeds");
        assert_eq!(value, Value::String("Ada Lovelace".into()));
    }

    #[test]
    fn struct_field_access_reports_missing_field() {
        let runtime = runtime_with_user();
        let err = eval(&runtime, "user.role").expect_err("missing field fails");
        assert!(
            err.to_string().contains("does not contain field 'role'"),
            "{err}"
        );
    }

    #[test]
    fn calling_unregistered_function_errors() {
        let runtime = Runtime::builder().build();
        let err = eval(&runtime, "missing()")
            .expect_err("unknown function should produce error");
        assert!(
            err.to_string()
                .contains("Function 'missing' is not registered"),
            "{err}"
        );
    }

    #[test]
    fn comprehension_macros_allow_function_calls() {
        let runtime = runtime_with_assets();

        let has_high_risk =
            eval(&runtime, "exists(assets, asset, asset.risk >= 75)")
                .expect("exists() macro should evaluate");
        assert_eq!(has_high_risk, Value::Bool(true));

        let prod_names = eval(&runtime, "map(assets, asset, asset.name)")
            .expect("map() macro should evaluate");
        assert_eq!(prod_names, vec!["scanner", "api", "etl"].into_value());

        let filtered =
            eval(&runtime, "filter(assets, asset, asset.risk >= 75)")
                .expect("filter() macro should evaluate");
        assert_eq!(
            filtered,
            Value::List(ListValue::from(vec![asset(
                "scanner",
                80,
                &["prod", "pci"],
            )])),
        );
    }

    fn runtime_with_user() -> Runtime {
        let mut builder = Runtime::builder();
        let mut user = StructValue::new("example.User");
        user.set_field("name", "Ada Lovelace");
        user.set_field("active", true);
        builder
            .set_variable("user", Value::Struct(user))
            .expect("user variable to set");
        builder.build()
    }

    fn runtime_with_assets() -> Runtime {
        let mut builder = Runtime::builder();
        builder
            .set_variable("assets", sample_assets())
            .expect("assets variable to set");
        builder.build()
    }

    fn sample_assets() -> Value {
        Value::List(ListValue::from(vec![
            asset("scanner", 80, &["prod", "pci"]),
            asset("api", 65, &["prod"]),
            asset("etl", 40, &["batch"]),
        ]))
    }

    fn asset(name: &str, risk: i64, tags: &[&str]) -> Value {
        let mut record = MapValue::new();
        record.insert("name", name);
        record.insert("risk", risk);
        record.insert("tags", ListValue::from(tags.to_vec()));
        Value::Map(record)
    }
}
