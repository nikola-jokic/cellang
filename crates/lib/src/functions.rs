use crate::{
    eval_ast,
    parser::{Atom, Op, TokenTree},
    types::{Duration, List, Map},
    Environment, Key, KeyType, Value,
};
use miette::{Context, Error, IntoDiagnostic};
use regex::Regex;
use time::{format_description::well_known::Rfc3339, OffsetDateTime};

/// Returns the size of a value.
/// The value type must be one of the following:
/// - string
/// - list
/// - map
/// - bytes
pub fn size(env: &Environment, tokens: &[TokenTree]) -> Result<Value, Error> {
    if tokens.len() != 1 {
        miette::bail!("Expected 1 argument, found {}", tokens.len());
    }

    let v = match eval_ast(env, &tokens[0])?.to_value()? {
        Value::Bytes(b) => Value::Int(b.len() as i64),
        Value::String(s) => Value::Int(s.len() as i64),
        Value::List(list) => Value::Int(list.len() as i64),
        Value::Map(map) => Value::Int(map.len() as i64),
        _ => miette::bail!("Invalid type for size: {:?}", tokens[0]),
    };

    Ok(v)
}

/// Returns the type of a value as a Value::String.
/// All value types are supported.
pub fn type_fn(
    env: &Environment,
    tokens: &[TokenTree],
) -> Result<Value, Error> {
    if tokens.len() != 1 {
        miette::bail!("Expected 1 argument, found {}", tokens.len());
    }

    let v = match eval_ast(env, &tokens[0])?.to_value()? {
        Value::Int(_) => "int".into(),
        Value::Uint(_) => "uint".into(),
        Value::Double(_) => "double".into(),
        Value::String(_) => "string".into(),
        Value::Bool(_) => "bool".into(),
        Value::Map(_) => "map".into(),
        Value::List(_) => "list".into(),
        Value::Bytes(_) => "bytes".into(),
        Value::Null => "null".into(),
        Value::Timestamp(_) => "timestamp".into(),
        Value::Duration(_) => "duration".into(),
    };

    Ok(v)
}

/// Tests whether a field is available
pub fn has(env: &Environment, tokens: &[TokenTree]) -> Result<Value, Error> {
    if tokens.len() != 1 {
        miette::bail!("expected 1 argument, found {}", tokens.len());
    }

    match &tokens[0] {
        TokenTree::Cons(op, tokens) if matches!(op, Op::Field | Op::Index) => {
            let lhs = eval_ast(env, &tokens[0])?;
            let map = match lhs.try_value()? {
                Value::Map(m) => m,
                _ => miette::bail!("Invalid type for has: {:?}", tokens[0]),
            };

            match &tokens[1] {
                TokenTree::Atom(Atom::Ident(ident)) => {
                    if !matches!(*op, Op::Field) {
                        miette::bail!("Invalid type for has: {:?}", tokens[0]);
                    }
                    let key = Key::from(*ident);
                    Ok(Value::Bool(map.contains_key(&key)?))
                }
                TokenTree::Cons(_, tokens) => {
                    let mut env = env.child();
                    env.set_variables(map);
                    has(&env, tokens)
                }
                tree => miette::bail!("Invalid type for has: {:?}", tree),
            }
        }
        tree => miette::bail!("Invalid type for has: {:?}", tree),
    }
}

/// Tests whether all elements in the input list or all keys in a map satisfy the given predicate. The all macro behaves in a manner consistent with the Logical AND operator including in how it absorbs errors and short-circuits.
pub fn all(env: &Environment, tokens: &[TokenTree]) -> Result<Value, Error> {
    if tokens.len() != 3 {
        miette::bail!("expected 3 arguments, found {}", tokens.len());
    }

    // expect first parameter to be a list
    let lhs = eval_ast(env, &tokens[0])?;
    let host = match lhs.try_value()? {
        v if matches!(v, Value::List(_) | Value::Map(_)) => v,
        _ => miette::bail!("Invalid host type for all: {:?}", tokens[0]),
    };

    // expect second parameter to be an identifier
    let key = match &tokens[1] {
        TokenTree::Atom(Atom::Ident(ident)) => Key::from(*ident),
        _ => miette::bail!("Invalid identifier type for all: {:?}", tokens[1]),
    };

    // expect third parameter to be a lambda
    let lambda = &tokens[2];

    let mut variables = Map::with_type_and_capacity(KeyType::String, 1);

    let mut all = true;

    match host {
        Value::List(list) => {
            for item in list.iter() {
                variables.insert(key.clone(), item.clone())?;
                let mut env = env.child();
                env.set_variables(&variables);
                match eval_ast(&env, lambda)?.try_value()? {
                    Value::Bool(b) => {
                        if !b {
                            all = false;
                            break;
                        }
                    }
                    _ => miette::bail!(
                        "Invalid predicate type for all: {:?}",
                        lambda
                    ),
                }
            }
        }
        Value::Map(map) => {
            for value in map.keys() {
                variables.insert(key.clone(), value.into())?;
                let mut env = env.child();
                env.set_variables(&variables);
                match eval_ast(&env, lambda)?.try_value()? {
                    Value::Bool(b) => {
                        if !b {
                            all = false;
                            break;
                        }
                    }
                    _ => miette::bail!(
                        "Invalid predicate type for all: {:?}",
                        lambda
                    ),
                }
            }
        }
        _ => unreachable!(),
    }

    Ok(Value::Bool(all))
}

/// Tests whether any value in the list or any key in the map satisfies the predicate expression. The exists macro behaves in a manner consistent with the Logical OR operator including in how it absorbs errors and short-circuits.
pub fn exists(env: &Environment, tokens: &[TokenTree]) -> Result<Value, Error> {
    if tokens.len() != 3 {
        miette::bail!("expected 3 arguments, found {}", tokens.len());
    }

    // expect first parameter to be a list
    let lhs = eval_ast(env, &tokens[0])?;
    let host = match lhs.try_value()? {
        v if matches!(v, Value::List(_) | Value::Map(_)) => v,
        _ => miette::bail!("Invalid type for exists: {:?}", tokens[0]),
    };

    // expect second parameter to be an identifier
    let key = match &tokens[1] {
        TokenTree::Atom(Atom::Ident(ident)) => Key::from(*ident),
        _ => miette::bail!("Invalid type for exists: {:?}", tokens[1]),
    };

    // expect third parameter to be a lambda
    let lambda = &tokens[2];

    let mut variables = Map::with_type_and_capacity(KeyType::String, 1);

    let mut exists = false;
    match host {
        Value::List(list) => {
            for item in list.iter() {
                variables.insert(key.clone(), item.clone())?;
                let mut env = env.child();
                env.set_variables(&variables);
                match eval_ast(&env, lambda)?.try_value()? {
                    Value::Bool(b) => {
                        if *b {
                            exists = true;
                            break;
                        }
                    }
                    _ => miette::bail!("Invalid type for exists: {:?}", lambda),
                }
            }
        }
        Value::Map(map) => {
            for value in map.keys() {
                variables.insert(key.clone(), value.into())?;
                let mut env = env.child();
                env.set_variables(&variables);
                match eval_ast(&env, lambda)?.try_value()? {
                    Value::Bool(b) => {
                        if *b {
                            exists = true;
                            break;
                        }
                    }
                    _ => miette::bail!("Invalid type for exists: {:?}", lambda),
                }
            }
        }

        _ => unreachable!(),
    }

    Ok(Value::Bool(exists))
}

/// Tests whether exactly one list element or map key satisfies the predicate expression. This macro does not short-circuit in order to remain consistent with logical operators being the only operators which can absorb errors within CEL
pub fn exists_one(
    env: &Environment,
    tokens: &[TokenTree],
) -> Result<Value, Error> {
    if tokens.len() != 3 {
        miette::bail!("expected 3 arguments, found {}", tokens.len());
    }

    // expect first parameter to be a list
    let lhs = eval_ast(env, &tokens[0])?;
    let host = match lhs.to_value()? {
        v if matches!(v, Value::List(_) | Value::Map(_)) => v,
        _ => miette::bail!("Invalid type for exists_one: {:?}", tokens[0]),
    };

    // expect second parameter to be an identifier
    let key = match &tokens[1] {
        TokenTree::Atom(Atom::Ident(ident)) => Key::from(*ident),
        _ => miette::bail!("Invalid type for exists_one: {:?}", tokens[1]),
    };

    // expect third parameter to be a lambda
    let lambda = &tokens[2];

    let mut variables = Map::with_type_and_capacity(KeyType::String, 1);

    let mut found = false;
    match host {
        Value::List(list) => {
            for item in list.iter() {
                variables.insert(key.clone(), item.clone())?;
                let mut env = env.child();
                env.set_variables(&variables);
                match eval_ast(&env, lambda)?.try_value()? {
                    Value::Bool(b) => {
                        if *b {
                            if found {
                                found = false;
                                break;
                            }
                            found = true;
                        }
                    }
                    _ => miette::bail!(
                        "Invalid type for exists_one: {:?}",
                        lambda
                    ),
                }
            }
        }
        Value::Map(map) => {
            for value in map.keys() {
                variables.insert(key.clone(), value.into())?;
                let mut env = env.child();
                env.set_variables(&variables);
                match eval_ast(&env, lambda)?.try_value()? {
                    Value::Bool(b) => {
                        if *b {
                            if found {
                                found = false;
                                break;
                            }
                            found = true;
                        }
                    }
                    _ => miette::bail!(
                        "Invalid type for exists_one: {:?}",
                        lambda
                    ),
                }
            }
        }
        _ => unreachable!(),
    }

    Ok(Value::Bool(found))
}

/// Returns a list where each element is the result of applying the transform expression to the corresponding input list element or input map key.
/// There are two forms of map macro:
/// - The three argument form transforms all elements.
/// - The four argument form transforms only elements which satisfy the predicate.
///
/// The four argument form of the macro exists to simplify combined filter / map operations.
pub fn map(env: &Environment, tokens: &[TokenTree]) -> Result<Value, Error> {
    if tokens.len() != 3 && tokens.len() != 4 {
        miette::bail!("expected 3 or 4 arguments, found {}", tokens.len());
    }

    // Host the value reference
    let lhs;

    // If there are 3 arguments, no filtering is needed
    let this = if tokens.len() == 3 {
        lhs = eval_ast(env, &tokens[0])?;
        match lhs.try_value()? {
            v if matches!(v, Value::List(_)) => v,
            Value::Map(map) => {
                &Value::List(map.keys().map(Value::from).collect())
            }
            _ => miette::bail!("Invalid type for map: {:?}", tokens[0]),
        }
    } else {
        &filter(env, &tokens[0..3])?
    };

    let key = match &tokens[1] {
        TokenTree::Atom(Atom::Ident(ident)) => Key::from(*ident),
        _ => miette::bail!("Invalid type for map: {:?}", tokens[1]),
    };

    let lambda = if tokens.len() == 3 {
        &tokens[2]
    } else {
        &tokens[3]
    };

    match this {
        Value::List(list) => {
            if list.is_empty() {
                return Ok(Value::List(list.clone())); // preserve type if set
            }
            let mut new_list = List::with_capacity(list.len());
            let mut variables = Map::with_type_and_capacity(KeyType::String, 1);
            for item in list.iter() {
                variables.insert(key.clone(), item.clone()).wrap_err(
                    "Invalid item insert, key={key:?}, value={item:?}",
                )?;
                let mut env = env.child();
                env.set_variables(&variables);
                new_list.push(eval_ast(&env, lambda)?.to_value()?)?;
            }
            Ok(Value::List(new_list))
        }
        v => Err(miette::miette!("Expected list, got {v:?}")),
    }
}

/// Returns a list containing only the elements from the input list that satisfy the given predicate.
/// The host type must be a list or a map.
pub fn filter(env: &Environment, tokens: &[TokenTree]) -> Result<Value, Error> {
    if tokens.len() != 3 {
        miette::bail!("expected 2 arguments, found {}", tokens.len());
    }

    let lhs = eval_ast(env, &tokens[0])?;
    let host = match lhs.try_value()? {
        v if matches!(v, Value::List(_) | Value::Map(_)) => v,
        _ => miette::bail!("Invalid type for filter: {:?}", tokens[0]),
    };

    // expect second parameter to be an identifier
    let key = match &tokens[1] {
        TokenTree::Atom(Atom::Ident(ident)) => Key::from(*ident),
        _ => miette::bail!("Invalid type for exists_one: {:?}", tokens[1]),
    };

    // expect third parameter to be a lambda
    let lambda = &tokens[2];

    let mut variables = Map::with_type_and_capacity(KeyType::String, 1);

    match host {
        Value::List(list) => {
            let mut new_list = List::with_type_and_capacity(
                list.element_type().unwrap(),
                list.len(),
            );
            for item in list.iter() {
                variables.insert(key.clone(), item.clone())?;
                let mut env = env.child();
                env.set_variables(&variables);
                match eval_ast(&env, lambda)?.try_value()? {
                    Value::Bool(b) => {
                        if *b {
                            new_list.push(item.clone())?;
                        }
                    }
                    _ => miette::bail!("Invalid type for filter: {:?}", lambda),
                }
            }
            Ok(Value::List(new_list))
        }
        Value::Map(map) => {
            let mut result = List::new();
            for k in map.keys() {
                variables.insert(key.clone(), k.clone().into())?;
                let mut env = env.child();
                env.set_variables(&variables);
                match eval_ast(&env, lambda)?.try_value()? {
                    Value::Bool(b) => {
                        if *b {
                            result.push(k.into())?;
                        }
                    }
                    _ => miette::bail!("Invalid type for filter: {:?}", lambda),
                }
            }
            Ok(Value::List(result))
        }
        _ => unreachable!(),
    }
}

/// Tests whether the string operand contains the substring. Time complexity is proportional to the product of the sizes of the arguments.
pub fn contains(
    env: &Environment,
    tokens: &[TokenTree],
) -> Result<Value, Error> {
    if tokens.len() != 2 {
        miette::bail!("expected 2 arguments, found {}", tokens.len());
    }

    let s = eval_ast(env, &tokens[0])?;
    let s = match s.try_value()? {
        Value::String(s) => s,
        _ => miette::bail!("Invalid type for contains: {:?}", tokens[0]),
    };

    let value = eval_ast(env, &tokens[1])?;
    let value = match value.try_value()? {
        Value::String(s) => s,
        _ => miette::bail!("Invalid type for contains: {:?}", tokens[1]),
    };

    Ok(Value::Bool(s.contains(value.as_str())))
}

/// Tests whether the string operand starts with the specified prefix. Average time complexity is linear with respect to the size of the prefix. Worst-case time complexity is proportional to the product of the sizes of the arguments.
pub fn starts_with(
    env: &Environment,
    tokens: &[TokenTree],
) -> Result<Value, Error> {
    if tokens.len() != 2 {
        miette::bail!("expected 2 arguments, found {}", tokens.len());
    }

    let s = eval_ast(env, &tokens[0])?;
    let s = match s.try_value()? {
        Value::String(s) => s,
        _ => miette::bail!("Invalid type for starts_with: {:?}", tokens[0]),
    };

    let value = eval_ast(env, &tokens[1])?;
    let value = match value.try_value()? {
        Value::String(s) => s,
        _ => miette::bail!("Invalid type for starts_with: {:?}", tokens[1]),
    };

    Ok(Value::Bool(s.starts_with(value.as_str())))
}

/// Tests whether the string operand ends with the specified suffix. Average time complexity is linear with respect to the size of the suffix string. Worst-case time complexity is proportional to the product of the sizes of the arguments.
pub fn ends_with(
    env: &Environment,
    tokens: &[TokenTree],
) -> Result<Value, Error> {
    if tokens.len() != 2 {
        miette::bail!("expected 2 arguments, found {}", tokens.len());
    }

    let s = eval_ast(env, &tokens[0])?;
    let s = match s.try_value()? {
        Value::String(s) => s,
        _ => miette::bail!("Invalid type for starts_with: {:?}", tokens[0]),
    };

    let value = eval_ast(env, &tokens[1])?;
    let value = match value.try_value()? {
        Value::String(s) => s,
        _ => miette::bail!("Invalid type for starts_with: {:?}", tokens[1]),
    };

    Ok(Value::Bool(s.ends_with(value.as_str())))
}

/// Tests whether a string matches a rust regular expression. This differs from the
/// original CEL documentation where RE2 expressions are used.
/// If needed, RE2 implementation can be done
pub fn matches(
    env: &Environment,
    tokens: &[TokenTree],
) -> Result<Value, Error> {
    if tokens.len() != 2 {
        miette::bail!("expected 2 arguments, found {}", tokens.len());
    }

    let s = eval_ast(env, &tokens[0])?;
    let s = match s.try_value()? {
        Value::String(s) => s,
        _ => miette::bail!("Invalid type for matches: {:?}", tokens[0]),
    };

    let value = eval_ast(env, &tokens[1])?;
    let value = match value.try_value()? {
        Value::String(s) => s,
        _ => miette::bail!("Invalid type for matches: {:?}", tokens[1]),
    };

    let re = Regex::new(value.as_str());

    match re {
        Ok(re) => Ok(Value::Bool(re.is_match(s.as_str()))),
        Err(e) => miette::bail!("Invalid regex: {}", e),
    }
}

/// Type denotation
pub fn uint(env: &Environment, tokens: &[TokenTree]) -> Result<Value, Error> {
    if tokens.len() != 1 {
        miette::bail!("expected 1 argument, found {}", tokens.len());
    }

    let v = match eval_ast(env, &tokens[0])?.to_value()? {
        Value::Int(i) => Value::Uint(u64::try_from(i).into_diagnostic()?),
        Value::Uint(u) => Value::Uint(u),
        Value::Double(d) => {
            let i = d as i64;
            Value::Uint(u64::try_from(i).into_diagnostic()?)
        }
        Value::String(s) => match s.parse::<u64>() {
            Ok(u) => Value::Uint(u),
            Err(_) => miette::bail!("Invalid type for uint: {:?}", tokens[0]),
        },
        _ => miette::bail!("Invalid type for uint: {:?}", tokens[0]),
    };

    Ok(v)
}

/// Type denotation
pub fn int(env: &Environment, tokens: &[TokenTree]) -> Result<Value, Error> {
    if tokens.len() != 1 {
        miette::bail!("expected 1 argument, found {}", tokens.len());
    }

    let v = match eval_ast(env, &tokens[0])?.to_value()? {
        Value::Int(i) => Value::Int(i),
        Value::Uint(u) => Value::Int(u as i64),
        Value::Double(d) => Value::Int(d as i64),
        Value::String(s) => match s.parse::<i64>() {
            Ok(i) => Value::Int(i),
            Err(_) => miette::bail!("Invalid type for int: {:?}", tokens[0]),
        },
        Value::Timestamp(t) => Value::Int(t.unix_timestamp()),
        _ => miette::bail!("Invalid type for int: {:?}", tokens[0]),
    };

    Ok(v)
}

/// Type denotation
/// string(string) -> string (identity)
/// string(bool) -> string converts true to "true" and false to "false"
/// string(int) -> string converts integer values to base 10 representation
/// string(uint) -> string converts unsigned integer values to base 10 representation
/// string(double) -> string converts a double to a string
/// string(bytes) -> string converts a byte sequence to a utf-8 string
/// string(timestamp) -> string converts a timestamp value to RFC3339 format
/// string(duration) -> string converts a duration value to seconds and fractional seconds with an 's' suffix
pub fn string(env: &Environment, tokens: &[TokenTree]) -> Result<Value, Error> {
    if tokens.len() != 1 {
        miette::bail!("expected 1 argument, found {}", tokens.len());
    }

    let v = match eval_ast(env, &tokens[0])?.to_value()? {
        Value::Int(i) => i.to_string().into(),
        Value::Uint(u) => u.to_string().into(),
        Value::Double(d) => d.to_string().into(),
        Value::String(s) => s.into(),
        Value::Bytes(s) => String::from_utf8_lossy(&s).to_string().into(),
        Value::Bool(b) => b.to_string().into(),
        Value::Null => "null".into(),
        Value::Timestamp(t) => t.format(&Rfc3339).into_diagnostic()?.into(),
        Value::Duration(d) => {
            dbg!(&d);
            dbg!(d.whole_seconds());
            let total_seconds = d.whole_seconds() as f64
                + (d.subsec_milliseconds() as f64 / 1000f64);
            format!("{}s", total_seconds).into()
        }
        _ => miette::bail!("Invalid type for string: {:?}", tokens[0]),
    };

    Ok(v)
}

/// Type conversion, according to RFC3339
pub fn timestamp(
    env: &Environment,
    tokens: &[TokenTree],
) -> Result<Value, Error> {
    if tokens.len() != 1 {
        miette::bail!("expected 1 argument, found {}", tokens.len());
    }

    let v = match eval_ast(env, &tokens[0])?.to_value()? {
        v if matches!(v, Value::Timestamp(_)) => v,
        Value::String(s) => {
            let t = match OffsetDateTime::parse(&s, &Rfc3339) {
                Ok(t) => t,
                Err(e) => miette::bail!("Invalid timestamp: {:?}", e),
            };

            Value::Timestamp(t)
        }
        _ => miette::bail!("Invalid type for timestamp: {:?}", tokens[0]),
    };

    Ok(v)
}

pub fn dyn_fn(env: &Environment, tokens: &[TokenTree]) -> Result<Value, Error> {
    if tokens.len() != 1 {
        miette::bail!("expected 1 argument, found {}", tokens.len());
    }

    let v = eval_ast(env, &tokens[0])?.to_value()?;

    Ok(v)
}

pub fn duration(
    env: &Environment,
    tokens: &[TokenTree],
) -> Result<Value, Error> {
    if tokens.len() != 1 {
        miette::bail!("expected 1 argument, found {}", tokens.len());
    }

    let v = match eval_ast(env, &tokens[0])?.to_value()? {
        Value::String(s) => {
            let d = s.parse::<Duration>()?;
            Value::Duration(d.0)
        }
        _ => miette::bail!("Invalid type for duration: {:?}", tokens[0]),
    };

    Ok(v)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{EnvironmentBuilder, Function, Parser};
    use std::{collections::HashMap, sync::Arc};

    fn is_function(_: Function) {}

    #[test]
    fn implement_functions() {
        is_function(Arc::new(size));
        is_function(Arc::new(type_fn));
        is_function(Arc::new(has));
        is_function(Arc::new(all));
        is_function(Arc::new(exists));
        is_function(Arc::new(exists_one));
        is_function(Arc::new(map));
        is_function(Arc::new(filter));
        is_function(Arc::new(contains));
        is_function(Arc::new(starts_with));
        is_function(Arc::new(matches));
        is_function(Arc::new(uint));
        is_function(Arc::new(int));
        is_function(Arc::new(string));
        is_function(Arc::new(dyn_fn));
        is_function(Arc::new(duration));
        is_function(Arc::new(timestamp));
    }

    #[test]
    fn test_size_primitive() {
        let env = EnvironmentBuilder::default();
        let env = env.build();

        for tt in [
            ("b'hello'", Value::Int(5)),
            ("'hello'", Value::Int(5)),
            ("[1, 2, 3]", Value::Int(3)),
            ("{'a': 1, 'b': 2}", Value::Int(2)),
        ] {
            let program = tt.0;
            let tree = Parser::new(program).parse().unwrap();
            let v = size(&env, &[tree]);
            assert!(
                v.is_ok(),
                "expected ok got err: program='{program}, result={:?}",
                v
            );
            assert_eq!(v.unwrap(), tt.1);
        }

        for tt in ["1", "1.0", "true", "null"] {
            let program = tt;
            let tree = Parser::new(program).parse().unwrap();
            let v = size(&env, &[tree]);
            assert!(
                v.is_err(),
                "expected err got ok: program='{program}, result={:?}",
                v
            );
        }
    }

    #[test]
    fn test_type_fn_primitive() {
        let env = EnvironmentBuilder::default();
        let env = env.build();

        for tt in [
            ("1", "int".into()),
            ("1u", "uint".into()),
            ("1.0", "double".into()),
            ("true", "bool".into()),
            ("'hello'", "string".into()),
            ("null", "null".into()),
            ("[1, 2, 3]", "list".into()),
            ("{'a': 1, 'b': 2}", "map".into()),
            ("b'hello'", "bytes".into()),
        ] {
            let program = tt.0;
            let tree = Parser::new(program).parse().unwrap();
            let v = type_fn(&env, &[tree]);
            assert!(
                v.is_ok(),
                "expected ok got err: program='{program}, result={:?}",
                v
            );
            assert_eq!(v.unwrap(), tt.1);
        }
    }

    #[test]
    fn test_has() {
        let mut env = EnvironmentBuilder::default();
        env.set_variable(
            Key::from("a"),
            Value::Map(
                Map::new()
                    .insert(
                        Key::Int(0),
                        Value::Map(
                            Map::new()
                                .insert(Key::from("b"), Value::Int(1))
                                .unwrap()
                                .to_owned(),
                        ),
                    )
                    .unwrap()
                    .to_owned(),
            )
            .to_owned(),
        )
        .unwrap();

        let program = "a[0].b";
        let tree = Parser::new(program).parse().unwrap();
        let env = env.build();
        let v = has(&env, &[tree]);
        assert!(
            v.is_ok(),
            "expected ok got err: program='{program}, result={v:?}"
        );
        let v = v.unwrap();
        assert_eq!(v, Value::Bool(true));

        let program = "a[0].c";
        let tree = Parser::new(program).parse().unwrap();
        let v = has(&env, &[tree]);
        assert!(
            v.is_ok(),
            "expected ok got err: program='{program}, result={v:?}"
        );
        let v = v.unwrap();
        assert_eq!(v, Value::Bool(false));

        let program = "a[1]";
        let tree = Parser::new(program).parse().unwrap();
        let v = has(&env, &[tree]);
        assert!(
            v.is_err(),
            "expected err got ok: program='{program}, result={v:?}"
        );
    }

    #[test]
    fn test_all_list() {
        let mut env = EnvironmentBuilder::default();
        env.set_variable(
            Key::from("list"),
            Value::List(
                List::new()
                    .push(Value::Int(1))
                    .unwrap()
                    .push(Value::Int(2))
                    .unwrap()
                    .push(Value::Int(3))
                    .unwrap()
                    .to_owned(),
            )
            .to_owned(),
        )
        .unwrap();

        let ident = TokenTree::Atom(Atom::Ident("x"));
        let lambda = Parser::new("x > 0").parse().unwrap();

        let env = env.build();
        let result =
            all(&env, &[TokenTree::Atom(Atom::Ident("list")), ident, lambda]);
        assert!(result.is_ok(), "expected ok got err: result={:?}", result);
        assert_eq!(result.unwrap(), Value::Bool(true));

        let lambda = Parser::new("x > 1").parse().unwrap();
        let ident = TokenTree::Atom(Atom::Ident("x"));
        let result =
            all(&env, &[TokenTree::Atom(Atom::Ident("list")), ident, lambda]);
        assert!(result.is_ok(), "expected ok got err: result={:?}", result);
        assert_eq!(result.unwrap(), Value::Bool(false));

        let lambda = Parser::new("y > 1").parse().unwrap();
        let ident = TokenTree::Atom(Atom::Ident("x"));
        let result =
            all(&env, &[TokenTree::Atom(Atom::Ident("list")), ident, lambda]);
        assert!(result.is_err(), "expected err got ok: result={:?}", result);
    }

    #[test]
    fn test_all_map() {
        let mut env = EnvironmentBuilder::default();
        env.set_variable(
            Key::from("m"),
            Value::Map(
                Map::new()
                    .insert(Key::from("a"), Value::Int(1))
                    .unwrap()
                    .insert(Key::from("b"), Value::Int(2))
                    .unwrap()
                    .insert(Key::from("c"), Value::Int(3))
                    .unwrap()
                    .to_owned(),
            )
            .to_owned(),
        )
        .unwrap();

        let ident = TokenTree::Atom(Atom::Ident("x"));
        let lambda = Parser::new("x >= 'a' && x <= 'z'").parse().unwrap();

        let env = env.build();
        let result =
            all(&env, &[TokenTree::Atom(Atom::Ident("m")), ident, lambda]);
        assert!(result.is_ok(), "expected ok got err: result={:?}", result);
        assert_eq!(result.unwrap(), Value::Bool(true));

        let ident = TokenTree::Atom(Atom::Ident("x"));
        let lambda = Parser::new("x > 'a'").parse().unwrap();
        let result =
            all(&env, &[TokenTree::Atom(Atom::Ident("m")), ident, lambda]);
        assert!(result.is_ok(), "expected ok got err: result={:?}", result);
        assert_eq!(result.unwrap(), Value::Bool(false));

        let ident = TokenTree::Atom(Atom::Ident("x"));
        let lambda = Parser::new("y > 'a'").parse().unwrap();
        let result =
            all(&env, &[TokenTree::Atom(Atom::Ident("m")), ident, lambda]);
        assert!(result.is_err(), "expected err got ok: result={:?}", result);
    }

    #[test]
    fn test_exists_list() {
        let mut env = EnvironmentBuilder::default();
        env.set_variable(
            Key::from("list"),
            Value::List(
                List::new()
                    .push(Value::Int(1))
                    .unwrap()
                    .push(Value::Int(2))
                    .unwrap()
                    .push(Value::Int(3))
                    .unwrap()
                    .to_owned(),
            )
            .to_owned(),
        )
        .unwrap();

        let ident = TokenTree::Atom(Atom::Ident("x"));
        let lambda = Parser::new("x > 2").parse().unwrap();

        let env = env.build();
        let result = exists(
            &env,
            &[TokenTree::Atom(Atom::Ident("list")), ident, lambda],
        );
        assert!(result.is_ok(), "expected ok got err: result={:?}", result);
        assert_eq!(result.unwrap(), Value::Bool(true));

        let ident = TokenTree::Atom(Atom::Ident("x"));
        let lambda = Parser::new("x > 3").parse().unwrap();
        let result = exists(
            &env,
            &[TokenTree::Atom(Atom::Ident("list")), ident, lambda],
        );
        assert!(result.is_ok(), "expected ok got err: result={:?}", result);
        assert_eq!(result.unwrap(), Value::Bool(false));

        let ident = TokenTree::Atom(Atom::Ident("x"));
        let lambda = Parser::new("y > 1").parse().unwrap();
        let result = exists(
            &env,
            &[TokenTree::Atom(Atom::Ident("list")), ident, lambda],
        );
        assert!(result.is_err(), "expected err got ok: result={:?}", result);
    }

    #[test]
    fn test_exists_map() {
        let mut env = EnvironmentBuilder::default();
        env.set_variable(
            Key::from("m"),
            Value::Map(
                Map::new()
                    .insert(Key::from("a"), Value::Int(1))
                    .unwrap()
                    .insert(Key::from("b"), Value::Int(2))
                    .unwrap()
                    .insert(Key::from("c"), Value::Int(3))
                    .unwrap()
                    .to_owned(),
            )
            .to_owned(),
        )
        .unwrap();

        let ident = TokenTree::Atom(Atom::Ident("x"));
        let lambda = Parser::new("x > 'b'").parse().unwrap();

        let env = env.build();
        let result =
            exists(&env, &[TokenTree::Atom(Atom::Ident("m")), ident, lambda]);
        assert!(result.is_ok(), "expected ok got err: result={:?}", result);
        assert_eq!(result.unwrap(), Value::Bool(true));

        let ident = TokenTree::Atom(Atom::Ident("x"));
        let lambda = Parser::new("x > 'z'").parse().unwrap();
        let result =
            exists(&env, &[TokenTree::Atom(Atom::Ident("m")), ident, lambda]);
        assert!(result.is_ok(), "expected ok got err: result={:?}", result);
        assert_eq!(result.unwrap(), Value::Bool(false));

        let ident = TokenTree::Atom(Atom::Ident("x"));
        let lambda = Parser::new("y > 'a'").parse().unwrap();
        let result =
            exists(&env, &[TokenTree::Atom(Atom::Ident("m")), ident, lambda]);
        assert!(result.is_err(), "expected err got ok: result={:?}", result);
    }

    #[test]
    fn test_exists_one_list() {
        let mut env = EnvironmentBuilder::default();
        env.set_variable(
            Key::from("list"),
            Value::List(
                List::new()
                    .push(Value::Int(1))
                    .unwrap()
                    .push(Value::Int(2))
                    .unwrap()
                    .push(Value::Int(3))
                    .unwrap()
                    .to_owned(),
            )
            .to_owned(),
        )
        .unwrap();

        let ident = TokenTree::Atom(Atom::Ident("x"));
        let lambda = Parser::new("x > 2").parse().unwrap();

        let env = env.build();
        let result = exists_one(
            &env,
            &[TokenTree::Atom(Atom::Ident("list")), ident, lambda],
        );
        assert!(result.is_ok(), "expected ok got err: result={:?}", result);
        assert_eq!(result.unwrap(), Value::Bool(true));

        let ident = TokenTree::Atom(Atom::Ident("x"));
        let lambda = Parser::new("x > 3").parse().unwrap();
        let result = exists_one(
            &env,
            &[TokenTree::Atom(Atom::Ident("list")), ident, lambda],
        );
        assert!(result.is_ok(), "expected ok got err: result={:?}", result);
        assert_eq!(result.unwrap(), Value::Bool(false));

        let ident = TokenTree::Atom(Atom::Ident("x"));
        let lambda = Parser::new("y > 1").parse().unwrap();
        let result = exists_one(
            &env,
            &[TokenTree::Atom(Atom::Ident("list")), ident, lambda],
        );
        assert!(result.is_err(), "expected err got ok: result={:?}", result);
    }

    #[test]
    fn test_exists_one_map() {
        let mut env = EnvironmentBuilder::default();
        env.set_variable(
            Key::from("m"),
            Value::Map(
                Map::new()
                    .insert(Key::from("a"), Value::Int(1))
                    .unwrap()
                    .insert(Key::from("b"), Value::Int(2))
                    .unwrap()
                    .insert(Key::from("c"), Value::Int(3))
                    .unwrap()
                    .to_owned(),
            )
            .to_owned(),
        )
        .unwrap();

        let ident = TokenTree::Atom(Atom::Ident("x"));
        let lambda = Parser::new("x > 'b'").parse().unwrap();

        let env = env.build();
        let result = exists_one(
            &env,
            &[TokenTree::Atom(Atom::Ident("m")), ident, lambda],
        );
        assert!(result.is_ok(), "expected ok got err: result={:?}", result);
        assert_eq!(result.unwrap(), Value::Bool(true));

        let ident = TokenTree::Atom(Atom::Ident("x"));
        let lambda = Parser::new("x > 'c'").parse().unwrap();
        let result = exists_one(
            &env,
            &[TokenTree::Atom(Atom::Ident("m")), ident, lambda],
        );
        assert!(result.is_ok(), "expected ok got err: result={:?}", result);
        assert_eq!(result.unwrap(), Value::Bool(false));

        let ident = TokenTree::Atom(Atom::Ident("x"));
        let lambda = Parser::new("y > 'a'").parse().unwrap();
        let result = exists_one(
            &env,
            &[TokenTree::Atom(Atom::Ident("m")), ident, lambda],
        );
        assert!(result.is_err(), "expected err got ok: result={:?}", result);
    }

    #[test]
    fn test_map_list_3_args() {
        let mut env = EnvironmentBuilder::default();
        env.set_variable(
            Key::from("list"),
            Value::List(
                List::new()
                    .push(Value::Int(1))
                    .unwrap()
                    .push(Value::Int(2))
                    .unwrap()
                    .push(Value::Int(3))
                    .unwrap()
                    .to_owned(),
            )
            .to_owned(),
        )
        .unwrap();

        let ident = TokenTree::Atom(Atom::Ident("x"));
        let lambda = Parser::new("x + 1").parse().unwrap();

        let env = env.build();
        let result =
            map(&env, &[TokenTree::Atom(Atom::Ident("list")), ident, lambda]);
        assert!(result.is_ok(), "expected ok got err: result={:?}", result);
        assert_eq!(
            result.unwrap(),
            Value::List(
                List::new()
                    .push(Value::Int(2))
                    .unwrap()
                    .push(Value::Int(3))
                    .unwrap()
                    .push(Value::Int(4))
                    .unwrap()
                    .to_owned()
            )
        );
    }

    #[test]
    fn test_map_map_3_args() {
        let mut env = EnvironmentBuilder::default();
        env.set_variable(
            Key::from("m"),
            Value::Map(
                Map::new()
                    .insert(Key::from("a"), Value::Int(1))
                    .unwrap()
                    .insert(Key::from("b"), Value::Int(2))
                    .unwrap()
                    .insert(Key::from("c"), Value::Int(3))
                    .unwrap()
                    .to_owned(),
            )
            .to_owned(),
        )
        .unwrap();

        let ident = TokenTree::Atom(Atom::Ident("x"));
        let lambda = Parser::new("m[x] + 1").parse().unwrap();

        let env = env.build();
        let result =
            map(&env, &[TokenTree::Atom(Atom::Ident("m")), ident, lambda])
                .expect("expected ok, got err on result");

        // For now, let's go with the sum until ordering is preserved
        match result {
            Value::List(l) => {
                let mut sum = 0i64;
                for val in l {
                    match val {
                        Value::Int(n) => sum += n,
                        v => panic!("expected int, got {v:?}"),
                    };
                }

                assert_eq!(9i64, sum);
            }
            res => panic!("expected list, got {res:?}"),
        }
    }

    #[test]
    fn test_map_list_4_args() {
        let mut env = EnvironmentBuilder::default();
        env.set_variable(
            Key::from("list"),
            Value::List(
                List::new()
                    .push(Value::Int(1))
                    .unwrap()
                    .push(Value::Int(2))
                    .unwrap()
                    .push(Value::Int(3))
                    .unwrap()
                    .to_owned(),
            )
            .to_owned(),
        )
        .unwrap();

        let ident = TokenTree::Atom(Atom::Ident("x"));
        let filter = Parser::new("x > 1").parse().unwrap();
        let lambda = Parser::new("x + 1").parse().unwrap();

        let env = env.build();
        let result = map(
            &env,
            &[TokenTree::Atom(Atom::Ident("list")), ident, filter, lambda],
        );
        assert!(result.is_ok(), "expected ok got err: result={:?}", result);
        assert_eq!(
            result.unwrap(),
            Value::List(
                List::new()
                    .push(Value::Int(3))
                    .unwrap()
                    .push(Value::Int(4))
                    .unwrap()
                    .to_owned()
            )
        );
    }

    #[test]
    fn test_map_map_4_args() {
        let mut env = EnvironmentBuilder::default();
        env.set_variable(
            Key::from("m"),
            Value::Map(
                Map::new()
                    .insert(Key::from("a"), Value::Int(1))
                    .unwrap()
                    .insert(Key::from("b"), Value::Int(2))
                    .unwrap()
                    .insert(Key::from("c"), Value::Int(3))
                    .unwrap()
                    .to_owned(),
            )
            .to_owned(),
        )
        .unwrap();

        let ident = TokenTree::Atom(Atom::Ident("x"));
        let filter = Parser::new("m[x] > 1").parse().unwrap();
        let lambda = Parser::new("m[x] + 1").parse().unwrap();

        let env = env.build();
        let result = map(
            &env,
            &[TokenTree::Atom(Atom::Ident("m")), ident, filter, lambda],
        )
        .expect("expected ok, got err");

        match result {
            Value::List(l) => {
                let mut sum = 0i64;
                for val in l {
                    match val {
                        Value::Int(n) => sum += n,
                        v => panic!("expected int, got {v:?}"),
                    };
                }

                assert_eq!(7i64, sum);
            }
            res => panic!("expected list, got {res:?}"),
        }
    }

    #[test]
    fn test_filter_list() {
        let mut env = EnvironmentBuilder::default();
        env.set_variable(
            Key::from("list"),
            Value::List(
                List::new()
                    .push(Value::Int(1))
                    .unwrap()
                    .push(Value::Int(2))
                    .unwrap()
                    .push(Value::Int(3))
                    .unwrap()
                    .to_owned(),
            )
            .to_owned(),
        )
        .unwrap();

        let ident = TokenTree::Atom(Atom::Ident("x"));
        let lambda = Parser::new("x > 1").parse().unwrap();

        let env = env.build();
        let result = filter(
            &env,
            &[TokenTree::Atom(Atom::Ident("list")), ident, lambda],
        );
        assert!(result.is_ok(), "expected ok got err: result={:?}", result);
        assert_eq!(
            result.unwrap(),
            Value::List(
                List::new()
                    .push(Value::Int(2))
                    .unwrap()
                    .push(Value::Int(3))
                    .unwrap()
                    .to_owned()
            )
        );
    }

    #[test]
    fn test_filter_map() {
        let mut env = crate::EnvironmentBuilder::default();
        env.set_variable(
            Key::from("m"),
            Value::Map(
                Map::new()
                    .insert(Key::from("a"), Value::Int(1))
                    .unwrap()
                    .insert(Key::from("b"), Value::Int(2))
                    .unwrap()
                    .insert(Key::from("c"), Value::Int(3))
                    .unwrap()
                    .to_owned(),
            )
            .to_owned(),
        )
        .unwrap();

        let ident = TokenTree::Atom(Atom::Ident("x"));
        let lambda = Parser::new("x > 'a'").parse().unwrap();

        let env = env.build();
        let result =
            filter(&env, &[TokenTree::Atom(Atom::Ident("m")), ident, lambda])
                .expect("expected ok, got err on filter");

        match result {
            Value::List(list) => {
                let want = {
                    let mut m = HashMap::new();
                    m.insert("b".to_string(), 1i64);
                    m.insert("c".to_string(), 1i64);
                    m
                };
                let mut got = HashMap::new();
                for item in list {
                    match item {
                        Value::String(s) => got.entry(s).or_insert(1),
                        v => panic!("Expected string, got {v:?}"),
                    };
                }
                assert_eq!(want, got)
            }
            v => panic!("Expected list, got {v:?}"),
        }
    }
}
