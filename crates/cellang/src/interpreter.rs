use crate::error::RuntimeError;
use crate::macros::{self, ComprehensionKind, MacroInvocation};
use crate::parser::{Atom, Op, Parser, TokenTree};
use crate::runtime::{CallContext, Runtime};
use crate::value::{Key, ListValue, MapValue, TryFromValue, Value, ValueError};
use std::cmp::Ordering;

/// Evaluates the given source string in the context of the provided runtime,
/// returning the resulting value.
pub fn eval(runtime: &Runtime, source: &str) -> Result<Value, RuntimeError> {
    let mut parser = Parser::new(source);
    let ast = parser.parse().map_err(RuntimeError::from)?;
    eval_ast(runtime, &ast)
}

/// Evaluates the given AST node in the context of the provided runtime,
/// returning the resulting value.
pub fn eval_ast<'src>(
    runtime: &Runtime,
    node: &TokenTree<'src>,
) -> Result<Value, RuntimeError> {
    let mut ctx = EvalContext::new(runtime);
    eval_expr(&mut ctx, node)
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

fn eval_expr<'src>(
    ctx: &mut EvalContext<'_>,
    node: &TokenTree<'src>,
) -> Result<Value, RuntimeError> {
    match node {
        TokenTree::Atom(atom) => eval_atom(ctx, atom),
        TokenTree::Cons(op, args) => eval_cons(ctx, *op, args),
        TokenTree::Call {
            func,
            args,
            is_method,
        } => eval_call(ctx, func, args, *is_method),
    }
}

fn eval_atom(
    ctx: &mut EvalContext<'_>,
    atom: &Atom<'_>,
) -> Result<Value, RuntimeError> {
    Ok(match atom {
        Atom::Bool(value) => Value::Bool(*value),
        Atom::Int(value) => Value::Int(*value),
        Atom::Uint(value) => Value::Uint(*value),
        Atom::Double(value) => Value::Double(*value),
        Atom::String(value) => Value::String(value.to_string()),
        Atom::Bytes(value) => Value::Bytes(value.to_vec()),
        Atom::Null => Value::Null,
        Atom::Ident(name) => ctx
            .resolve_identifier(name)
            .ok_or_else(|| RuntimeError::missing_identifier(name))?,
    })
}

fn eval_cons(
    ctx: &mut EvalContext<'_>,
    op: Op,
    args: &[TokenTree<'_>],
) -> Result<Value, RuntimeError> {
    match op {
        Op::Group => {
            ensure_arity(op, args, 1).and_then(|_| eval_expr(ctx, &args[0]))
        }
        Op::List => eval_list(ctx, args),
        Op::Map => eval_map(ctx, args),
        Op::Dyn => {
            ensure_arity(op, args, 1).and_then(|_| eval_expr(ctx, &args[0]))
        }
        Op::Not => {
            ensure_arity(op, args, 1)?;
            let value = eval_expr(ctx, &args[0])?;
            let flag = <bool as TryFromValue>::try_from_value(&value).map_err(
                |err| RuntimeError::with_source("expected bool", err),
            )?;
            Ok(Value::Bool(!flag))
        }
        Op::Minus => {
            if args.len() == 1 {
                let value = eval_expr(ctx, &args[0])?;
                negate_value(&value)
            } else {
                ensure_arity(op, args, 2)?;
                let left = eval_expr(ctx, &args[0])?;
                let right = eval_expr(ctx, &args[1])?;
                subtract_values(&left, &right)
            }
        }
        Op::Plus => {
            ensure_arity(op, args, 2)?;
            let left = eval_expr(ctx, &args[0])?;
            let right = eval_expr(ctx, &args[1])?;
            add_values(&left, &right)
        }
        Op::Multiply => {
            ensure_arity(op, args, 2)?;
            let left = eval_expr(ctx, &args[0])?;
            let right = eval_expr(ctx, &args[1])?;
            multiply_values(&left, &right)
        }
        Op::Devide => {
            ensure_arity(op, args, 2)?;
            let left = eval_expr(ctx, &args[0])?;
            let right = eval_expr(ctx, &args[1])?;
            divide_values(&left, &right)
        }
        Op::Mod => {
            ensure_arity(op, args, 2)?;
            let left = eval_expr(ctx, &args[0])?;
            let right = eval_expr(ctx, &args[1])?;
            modulo_values(&left, &right)
        }
        Op::And => {
            ensure_arity(op, args, 2)?;
            let left = eval_expr(ctx, &args[0])?;
            let left_flag = <bool as TryFromValue>::try_from_value(&left)
                .map_err(|err| {
                    RuntimeError::with_source("expected bool", err)
                })?;
            if !left_flag {
                return Ok(Value::Bool(false));
            }
            let right = eval_expr(ctx, &args[1])?;
            let right_flag = <bool as TryFromValue>::try_from_value(&right)
                .map_err(|err| {
                    RuntimeError::with_source("expected bool", err)
                })?;
            Ok(Value::Bool(right_flag))
        }
        Op::Or => {
            ensure_arity(op, args, 2)?;
            let left = eval_expr(ctx, &args[0])?;
            let left_flag = <bool as TryFromValue>::try_from_value(&left)
                .map_err(|err| {
                    RuntimeError::with_source("expected bool", err)
                })?;
            if left_flag {
                return Ok(Value::Bool(true));
            }
            let right = eval_expr(ctx, &args[1])?;
            let right_flag = <bool as TryFromValue>::try_from_value(&right)
                .map_err(|err| {
                    RuntimeError::with_source("expected bool", err)
                })?;
            Ok(Value::Bool(right_flag))
        }
        Op::EqualEqual | Op::NotEqual => {
            ensure_arity(op, args, 2)?;
            let left = eval_expr(ctx, &args[0])?;
            let right = eval_expr(ctx, &args[1])?;
            let eq = left == right;
            Ok(Value::Bool(if matches!(op, Op::EqualEqual) {
                eq
            } else {
                !eq
            }))
        }
        Op::Less | Op::LessEqual | Op::Greater | Op::GreaterEqual => {
            ensure_arity(op, args, 2)?;
            let left = eval_expr(ctx, &args[0])?;
            let right = eval_expr(ctx, &args[1])?;
            let ordering = compare_values(&left, &right)?;
            let result = match op {
                Op::Less => ordering == Ordering::Less,
                Op::LessEqual => ordering != Ordering::Greater,
                Op::Greater => ordering == Ordering::Greater,
                Op::GreaterEqual => ordering != Ordering::Less,
                _ => unreachable!(),
            };
            Ok(Value::Bool(result))
        }
        Op::IfTernary => {
            if args.len() != 3 {
                return Err(RuntimeError::new(
                    "ternary operator requires condition and two branches",
                ));
            }
            let condition = eval_expr(ctx, &args[0])?;
            let flag = <bool as TryFromValue>::try_from_value(&condition)
                .map_err(|err| {
                    RuntimeError::with_source("expected bool", err)
                })?;
            if flag {
                eval_expr(ctx, &args[1])
            } else {
                eval_expr(ctx, &args[2])
            }
        }
        Op::In => {
            ensure_arity(op, args, 2)?;
            let needle = eval_expr(ctx, &args[0])?;
            let haystack = eval_expr(ctx, &args[1])?;
            eval_in_operator(&needle, &haystack)
        }
        Op::Index => {
            ensure_arity(op, args, 2)?;
            let target = eval_expr(ctx, &args[0])?;
            let index = eval_expr(ctx, &args[1])?;
            eval_index(&target, &index)
        }
        Op::Field => {
            ensure_arity(op, args, 2)?;
            eval_field(ctx, &args[0], &args[1])
        }
        Op::Call | Op::For | Op::Var | Op::While => Err(RuntimeError::new(
            format!("Operator '{op:?}' is not supported in this context"),
        )),
    }
}

fn eval_list(
    ctx: &mut EvalContext<'_>,
    args: &[TokenTree<'_>],
) -> Result<Value, RuntimeError> {
    let mut list = ListValue::new();
    for expr in args {
        list.push(eval_expr(ctx, expr)?);
    }
    Ok(Value::List(list))
}

fn eval_map(
    ctx: &mut EvalContext<'_>,
    args: &[TokenTree<'_>],
) -> Result<Value, RuntimeError> {
    if !args.len().is_multiple_of(2) {
        return Err(RuntimeError::new(
            "map literal expects key/value pairs but received odd number of expressions",
        ));
    }
    let mut map = MapValue::new();
    for chunk in args.chunks(2) {
        let key_value = eval_expr(ctx, &chunk[0])?;
        let key = Key::try_from(&key_value).map_err(RuntimeError::from)?;
        let value = eval_expr(ctx, &chunk[1])?;
        map.insert(key, value);
    }
    Ok(Value::Map(map))
}

fn eval_call(
    ctx: &mut EvalContext<'_>,
    func: &TokenTree<'_>,
    args: &[TokenTree<'_>],
    is_method: bool,
) -> Result<Value, RuntimeError> {
    let name = resolve_function_name(func).ok_or_else(|| {
        RuntimeError::new("function calls must reference an identifier")
    })?;
    if let Some(invocation) = macros::detect_macro_call(
        ctx.runtime().macros(),
        &name,
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

fn resolve_function_name(expr: &TokenTree<'_>) -> Option<String> {
    match expr {
        TokenTree::Atom(Atom::Ident(name)) => Some((*name).to_string()),
        TokenTree::Cons(Op::Field, nodes) if nodes.len() == 2 => {
            let left = resolve_function_name(&nodes[0])?;
            let right = resolve_function_name(&nodes[1])?;
            Some(format!("{left}.{right}"))
        }
        _ => None,
    }
}

fn eval_macro(
    ctx: &mut EvalContext<'_>,
    invocation: MacroInvocation<'_>,
) -> Result<Value, RuntimeError> {
    match invocation {
        MacroInvocation::Has { target, field } => {
            eval_has_macro(ctx, target, field)
        }
        MacroInvocation::Comprehension {
            kind,
            range,
            var,
            predicate,
            transform,
        } => match kind {
            ComprehensionKind::All => {
                let predicate = predicate.expect("predicate validated");
                eval_all_macro(ctx, range, var, predicate)
            }
            ComprehensionKind::Exists => {
                let predicate = predicate.expect("predicate validated");
                eval_exists_macro(ctx, range, var, predicate)
            }
            ComprehensionKind::ExistsOne => {
                let predicate = predicate.expect("predicate validated");
                eval_exists_one_macro(ctx, range, var, predicate)
            }
            ComprehensionKind::Map => {
                let transform = transform.expect("transform validated");
                eval_map_macro(ctx, range, var, predicate, transform)
            }
            ComprehensionKind::Filter => {
                let predicate = predicate.expect("predicate validated");
                eval_filter_macro(ctx, range, var, predicate)
            }
        },
    }
}

fn eval_has_macro(
    ctx: &mut EvalContext<'_>,
    target_expr: &TokenTree<'_>,
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
    range_expr: &TokenTree<'_>,
    var: &str,
    predicate: &TokenTree<'_>,
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
    range_expr: &TokenTree<'_>,
    var: &str,
    predicate: &TokenTree<'_>,
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
    range_expr: &TokenTree<'_>,
    var: &str,
    predicate: &TokenTree<'_>,
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
    range_expr: &TokenTree<'_>,
    var: &str,
    predicate: Option<&TokenTree<'_>>,
    transform: &TokenTree<'_>,
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
    range_expr: &TokenTree<'_>,
    var: &str,
    predicate: &TokenTree<'_>,
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
    predicate: &TokenTree<'_>,
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
    predicate: &TokenTree<'_>,
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
    predicate: &TokenTree<'_>,
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
    predicate: Option<&TokenTree<'_>>,
    transform: &TokenTree<'_>,
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
    predicate: &TokenTree<'_>,
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
    target_expr: &TokenTree<'_>,
    field_expr: &TokenTree<'_>,
) -> Result<Value, RuntimeError> {
    let target = eval_expr(ctx, target_expr)?;
    let field_name = match field_expr {
        TokenTree::Atom(Atom::Ident(name)) => name.to_string(),
        TokenTree::Atom(Atom::String(value)) => value.to_string(),
        _ => {
            let value = eval_expr(ctx, field_expr)?;
            <String as TryFromValue>::try_from_value(&value).map_err(|err| {
                RuntimeError::with_source(
                    "field access expects identifier",
                    err,
                )
            })?
        }
    };

    match target {
        Value::Struct(strct) => {
            strct.get(&field_name).cloned().ok_or_else(|| {
                RuntimeError::new(format!(
                    "Struct '{}' does not contain field '{field_name}'",
                    strct.type_name
                ))
            })
        }
        Value::Map(map) => map.get_str(&field_name).cloned().ok_or_else(|| {
            RuntimeError::new(format!(
                "Map value does not contain key '{field_name}'"
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

fn ensure_arity(
    op: Op,
    args: &[TokenTree<'_>],
    expected: usize,
) -> Result<(), RuntimeError> {
    if args.len() != expected {
        Err(RuntimeError::new(format!(
            "Operator '{op:?}' expected {expected} arguments but received {}",
            args.len()
        )))
    } else {
        Ok(())
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
        record.insert(
            "tags",
            ListValue::from(tags.iter().copied().collect::<Vec<_>>()),
        );
        Value::Map(record)
    }
}
