use crate::Value;
use miette::Error;

pub fn size(vals: &[Value]) -> Result<Value, Error> {
    if vals.len() != 1 {
        miette::bail!("Expected 1 argument, found {}", vals.len());
    }

    let v = match &vals[0] {
        Value::Bytes(b) => Value::Int(b.len() as i64),
        Value::String(s) => Value::Int(s.len() as i64),
        Value::List(list) => Value::Int(list.len() as i64),
        Value::Map(map) => Value::Int(map.len() as i64),
        _ => miette::bail!("Invalid type for size: {:?}", vals[0].kind()),
    };

    Ok(v)
}

pub fn type_fn(vals: &[Value]) -> Result<Value, Error> {
    if vals.len() != 1 {
        miette::bail!("Expected 1 argument, found {}", vals.len());
    }

    match &vals[0] {
        Value::Int(_) => Ok(Value::String("int".to_string())),
        Value::Uint(_) => Ok(Value::String("uint".to_string())),
        Value::Double(_) => Ok(Value::String("double".to_string())),
        Value::String(_) => Ok(Value::String("string".to_string())),
        Value::Bool(_) => Ok(Value::String("bool".to_string())),
        Value::Map(_) => Ok(Value::String("map".to_string())),
        Value::List(_) => Ok(Value::String("list".to_string())),
        Value::Bytes(_) => Ok(Value::String("bytes".to_string())),
        Value::Null => Ok(Value::String("null".to_string())),
        Value::Any(v) => Ok(Value::String(type_fn(&[*v.clone()])?.to_string())),
    }
}
