use crate::error::RuntimeError;
use crate::parser::{Atom, Op, Parser, TokenTree};
use crate::runtime::{CallContext, Runtime};
use crate::value::{Key, ListValue, MapValue, TryFromValue, Value, ValueError};
use std::cmp::Ordering;

pub fn eval(runtime: &Runtime, source: &str) -> Result<Value, RuntimeError> {
    let mut parser = Parser::new(source);
    let ast = parser.parse().map_err(RuntimeError::from)?;
    eval_ast(runtime, &ast)
}

pub fn eval_ast<'src>(
    runtime: &Runtime,
    node: &TokenTree<'src>,
) -> Result<Value, RuntimeError> {
    match node {
        TokenTree::Atom(atom) => eval_atom(runtime, atom),
        TokenTree::Cons(op, args) => eval_cons(runtime, *op, args),
        TokenTree::Call { func, args, .. } => eval_call(runtime, func, args),
    }
}

fn eval_atom(
    runtime: &Runtime,
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
        Atom::Ident(name) => runtime
            .resolve_identifier(name)
            .ok_or_else(|| RuntimeError::missing_identifier(name))?,
    })
}

fn eval_cons(
    runtime: &Runtime,
    op: Op,
    args: &[TokenTree<'_>],
) -> Result<Value, RuntimeError> {
    match op {
        Op::Group => {
            ensure_arity(op, args, 1).and_then(|_| eval_ast(runtime, &args[0]))
        }
        Op::List => eval_list(runtime, args),
        Op::Map => eval_map(runtime, args),
        Op::Dyn => {
            ensure_arity(op, args, 1).and_then(|_| eval_ast(runtime, &args[0]))
        }
        Op::Not => {
            ensure_arity(op, args, 1)?;
            let value = eval_ast(runtime, &args[0])?;
            let flag = <bool as TryFromValue>::try_from_value(&value).map_err(
                |err| RuntimeError::with_source("expected bool", err),
            )?;
            Ok(Value::Bool(!flag))
        }
        Op::Minus => {
            if args.len() == 1 {
                let value = eval_ast(runtime, &args[0])?;
                negate_value(&value)
            } else {
                ensure_arity(op, args, 2)?;
                let left = eval_ast(runtime, &args[0])?;
                let right = eval_ast(runtime, &args[1])?;
                subtract_values(&left, &right)
            }
        }
        Op::Plus => {
            ensure_arity(op, args, 2)?;
            let left = eval_ast(runtime, &args[0])?;
            let right = eval_ast(runtime, &args[1])?;
            add_values(&left, &right)
        }
        Op::Multiply => {
            ensure_arity(op, args, 2)?;
            let left = eval_ast(runtime, &args[0])?;
            let right = eval_ast(runtime, &args[1])?;
            multiply_values(&left, &right)
        }
        Op::Devide => {
            ensure_arity(op, args, 2)?;
            let left = eval_ast(runtime, &args[0])?;
            let right = eval_ast(runtime, &args[1])?;
            divide_values(&left, &right)
        }
        Op::Mod => {
            ensure_arity(op, args, 2)?;
            let left = eval_ast(runtime, &args[0])?;
            let right = eval_ast(runtime, &args[1])?;
            modulo_values(&left, &right)
        }
        Op::And => {
            ensure_arity(op, args, 2)?;
            let left = eval_ast(runtime, &args[0])?;
            let left_flag = <bool as TryFromValue>::try_from_value(&left)
                .map_err(|err| {
                    RuntimeError::with_source("expected bool", err)
                })?;
            if !left_flag {
                return Ok(Value::Bool(false));
            }
            let right = eval_ast(runtime, &args[1])?;
            let right_flag = <bool as TryFromValue>::try_from_value(&right)
                .map_err(|err| {
                    RuntimeError::with_source("expected bool", err)
                })?;
            Ok(Value::Bool(right_flag))
        }
        Op::Or => {
            ensure_arity(op, args, 2)?;
            let left = eval_ast(runtime, &args[0])?;
            let left_flag = <bool as TryFromValue>::try_from_value(&left)
                .map_err(|err| {
                    RuntimeError::with_source("expected bool", err)
                })?;
            if left_flag {
                return Ok(Value::Bool(true));
            }
            let right = eval_ast(runtime, &args[1])?;
            let right_flag = <bool as TryFromValue>::try_from_value(&right)
                .map_err(|err| {
                    RuntimeError::with_source("expected bool", err)
                })?;
            Ok(Value::Bool(right_flag))
        }
        Op::EqualEqual | Op::NotEqual => {
            ensure_arity(op, args, 2)?;
            let left = eval_ast(runtime, &args[0])?;
            let right = eval_ast(runtime, &args[1])?;
            let eq = left == right;
            Ok(Value::Bool(if matches!(op, Op::EqualEqual) {
                eq
            } else {
                !eq
            }))
        }
        Op::Less | Op::LessEqual | Op::Greater | Op::GreaterEqual => {
            ensure_arity(op, args, 2)?;
            let left = eval_ast(runtime, &args[0])?;
            let right = eval_ast(runtime, &args[1])?;
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
            let condition = eval_ast(runtime, &args[0])?;
            let flag = <bool as TryFromValue>::try_from_value(&condition)
                .map_err(|err| {
                    RuntimeError::with_source("expected bool", err)
                })?;
            if flag {
                eval_ast(runtime, &args[1])
            } else {
                eval_ast(runtime, &args[2])
            }
        }
        Op::In => {
            ensure_arity(op, args, 2)?;
            let needle = eval_ast(runtime, &args[0])?;
            let haystack = eval_ast(runtime, &args[1])?;
            eval_in_operator(&needle, &haystack)
        }
        Op::Index => {
            ensure_arity(op, args, 2)?;
            let target = eval_ast(runtime, &args[0])?;
            let index = eval_ast(runtime, &args[1])?;
            eval_index(&target, &index)
        }
        Op::Field => {
            ensure_arity(op, args, 2)?;
            eval_field(runtime, &args[0], &args[1])
        }
        Op::Call | Op::For | Op::Var | Op::While => Err(RuntimeError::new(
            format!("Operator '{op:?}' is not supported in this context"),
        )),
    }
}

fn eval_list(
    runtime: &Runtime,
    args: &[TokenTree<'_>],
) -> Result<Value, RuntimeError> {
    let mut list = ListValue::new();
    for expr in args {
        list.push(eval_ast(runtime, expr)?);
    }
    Ok(Value::List(list))
}

fn eval_map(
    runtime: &Runtime,
    args: &[TokenTree<'_>],
) -> Result<Value, RuntimeError> {
    if !args.len().is_multiple_of(2) {
        return Err(RuntimeError::new(
            "map literal expects key/value pairs but received odd number of expressions",
        ));
    }
    let mut map = MapValue::new();
    for chunk in args.chunks(2) {
        let key_value = eval_ast(runtime, &chunk[0])?;
        let key = Key::try_from(&key_value).map_err(RuntimeError::from)?;
        let value = eval_ast(runtime, &chunk[1])?;
        map.insert(key, value);
    }
    Ok(Value::Map(map))
}

fn eval_call(
    runtime: &Runtime,
    func: &TokenTree<'_>,
    args: &[TokenTree<'_>],
) -> Result<Value, RuntimeError> {
    let name = resolve_function_name(func).ok_or_else(|| {
        RuntimeError::new("function calls must reference an identifier")
    })?;
    let handler = runtime.lookup_function(&name).ok_or_else(|| {
        RuntimeError::new(format!("Function '{name}' is not registered"))
    })?;
    let mut evaluated = Vec::with_capacity(args.len());
    for expr in args {
        evaluated.push(eval_ast(runtime, expr)?);
    }
    let context = CallContext::new(runtime, &evaluated);
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

fn eval_field(
    runtime: &Runtime,
    target_expr: &TokenTree<'_>,
    field_expr: &TokenTree<'_>,
) -> Result<Value, RuntimeError> {
    let target = eval_ast(runtime, target_expr)?;
    let field_name = match field_expr {
        TokenTree::Atom(Atom::Ident(name)) => name.to_string(),
        TokenTree::Atom(Atom::String(value)) => value.to_string(),
        _ => {
            let value = eval_ast(runtime, field_expr)?;
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
    use crate::value::{StructValue, Value};

    #[test]
    fn evaluates_arithmetic_with_variables() {
        let mut builder = Runtime::builder();
        builder.set_variable("x", Value::Int(6));
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

    fn runtime_with_user() -> Runtime {
        let mut builder = Runtime::builder();
        let mut user = StructValue::new("example.User");
        user.set_field("name", "Ada Lovelace");
        user.set_field("active", true);
        builder.set_variable("user", Value::Struct(user));
        builder.build()
    }
}
