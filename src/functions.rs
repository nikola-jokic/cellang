use crate::{eval_ast, parser::TokenTree, Environment, Value};
use miette::Error;

pub fn size(env: &Environment, vals: &[TokenTree]) -> Result<Value, Error> {
    if vals.len() != 1 {
        miette::bail!("Expected 1 argument, found {}", vals.len());
    }

    let v = match eval_ast(env, &vals[0])?.to_value(env)? {
        Value::Bytes(b) => Value::Int(b.len() as i64),
        Value::String(s) => Value::Int(s.len() as i64),
        Value::List(list) => Value::Int(list.len() as i64),
        Value::Map(map) => Value::Int(map.len() as i64),
        _ => miette::bail!("Invalid type for size: {:?}", vals[0]),
    };

    Ok(v)
}

pub fn type_fn(env: &Environment, vals: &[TokenTree]) -> Result<Value, Error> {
    if vals.len() != 1 {
        miette::bail!("Expected 1 argument, found {}", vals.len());
    }

    let v = match eval_ast(env, &vals[0])?.to_value(env)? {
        Value::Int(_) => Value::String("int".to_string()),
        Value::Uint(_) => Value::String("uint".to_string()),
        Value::Double(_) => Value::String("double".to_string()),
        Value::String(_) => Value::String("string".to_string()),
        Value::Bool(_) => Value::String("bool".to_string()),
        Value::Map(_) => Value::String("map".to_string()),
        Value::List(_) => Value::String("list".to_string()),
        Value::Bytes(_) => Value::String("bytes".to_string()),
        Value::Null => Value::String("null".to_string()),
        _ => miette::bail!("Invalid type for type: {:?}", vals[0]),
    };

    Ok(v)
}

pub fn has(env: &Environment, vals: &[TokenTree]) -> Result<Value, Error> {
    if vals.len() != 2 {
        miette::bail!("Expected 2 arguments, found {}", vals.len());
    }

    todo!()
}
