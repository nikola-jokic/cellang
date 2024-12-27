use crate::{
    eval_ast,
    parser::{Atom, Op, TokenTree},
    types::{List, Map},
    Environment, Key, KeyKind, Value,
};
use miette::Error;
use regex::Regex;
use time::{format_description::well_known::Iso8601, Duration, OffsetDateTime};

/// Returns the size of a value.
pub fn size(env: &Environment, tokens: &[TokenTree]) -> Result<Value, Error> {
    if tokens.len() != 1 {
        miette::bail!("Expected 1 argument, found {}", tokens.len());
    }

    let v = match eval_ast(env, &tokens[0])?.to_value(env)? {
        Value::Bytes(b) => Value::Int(b.len() as i64),
        Value::String(s) => Value::Int(s.len() as i64),
        Value::List(list) => Value::Int(list.len() as i64),
        Value::Map(map) => Value::Int(map.len() as i64),
        _ => miette::bail!("Invalid type for size: {:?}", tokens[0]),
    };

    Ok(v)
}

pub fn type_fn(env: &Environment, tokens: &[TokenTree]) -> Result<Value, Error> {
    if tokens.len() != 1 {
        miette::bail!("Expected 1 argument, found {}", tokens.len());
    }

    let v = match eval_ast(env, &tokens[0])?.to_value(env)? {
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

pub fn has(env: &Environment, tokens: &[TokenTree]) -> Result<Value, Error> {
    if tokens.len() != 1 {
        miette::bail!("expected 1 argument, found {}", tokens.len());
    }

    match &tokens[0] {
        TokenTree::Cons(op, tokens) if matches!(op, Op::Field | Op::Index) => {
            let map = match eval_ast(env, &tokens[0])?.to_value(env)? {
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
                TokenTree::Cons(_op, tokens) => {
                    let mut env = env.child();
                    env.set_variables(&map);
                    has(&env, tokens)
                }
                tree => miette::bail!("Invalid type for has: {:?}", tree),
            }
        }
        tree => miette::bail!("Invalid type for has: {:?}", tree),
    }
}

pub fn all(env: &Environment, tokens: &[TokenTree]) -> Result<Value, Error> {
    if tokens.len() != 3 {
        miette::bail!("expected 3 arguments, found {}", tokens.len());
    }

    // expect first parameter to be a list
    let host = match eval_ast(env, &tokens[0])?.to_value(env)? {
        v if matches!(v, Value::List(_) | Value::Map(_)) => v,
        _ => miette::bail!("Invalid type for all: {:?}", tokens[0]),
    };

    // expect second parameter to be an identifier
    let key = match &tokens[1] {
        TokenTree::Atom(Atom::Ident(ident)) => Key::from(*ident),
        _ => miette::bail!("Invalid type for all: {:?}", tokens[1]),
    };

    // expect third parameter to be a lambda
    let lambda = &tokens[2];

    let mut variables = Map::with_type_and_capacity(KeyKind::String, 1);

    let mut all = true;

    match host {
        Value::List(list) => {
            for item in list.iter() {
                variables.insert(key.clone(), item.clone())?;
                let mut env = env.child();
                env.set_variables(&variables);
                match eval_ast(&env, lambda)?.to_value(&env)? {
                    Value::Bool(b) => {
                        if !b {
                            all = false;
                            break;
                        }
                    }
                    _ => miette::bail!("Invalid type for all: {:?}", lambda),
                }
            }
        }
        Value::Map(map) => {
            for (_key, value) in map.iter() {
                variables.insert(key.clone(), value.clone())?;
                let mut env = env.child();
                env.set_variables(&variables);
                match eval_ast(&env, lambda)?.to_value(&env)? {
                    Value::Bool(b) => {
                        if !b {
                            all = false;
                            break;
                        }
                    }
                    _ => miette::bail!("Invalid type for all: {:?}", lambda),
                }
            }
        }
        _ => unreachable!(),
    }

    Ok(Value::Bool(all))
}

pub fn exists(env: &Environment, tokens: &[TokenTree]) -> Result<Value, Error> {
    if tokens.len() != 3 {
        miette::bail!("expected 3 arguments, found {}", tokens.len());
    }

    // expect first parameter to be a list
    let host = match eval_ast(env, &tokens[0])?.to_value(env)? {
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

    let mut variables = Map::with_type_and_capacity(KeyKind::String, 1);

    let mut exists = false;
    match host {
        Value::List(list) => {
            for item in list.iter() {
                variables.insert(key.clone(), item.clone())?;
                let mut env = env.child();
                env.set_variables(&variables);
                match eval_ast(&env, lambda)?.to_value(&env)? {
                    Value::Bool(b) => {
                        if b {
                            exists = true;
                            break;
                        }
                    }
                    _ => miette::bail!("Invalid type for exists: {:?}", lambda),
                }
            }
        }
        Value::Map(map) => {
            for (_key, value) in map.iter() {
                variables.insert(key.clone(), value.clone())?;
                let mut env = env.child();
                env.set_variables(&variables);
                match eval_ast(&env, lambda)?.to_value(&env)? {
                    Value::Bool(b) => {
                        if b {
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

pub fn exists_one(env: &Environment, tokens: &[TokenTree]) -> Result<Value, Error> {
    if tokens.len() != 3 {
        miette::bail!("expected 3 arguments, found {}", tokens.len());
    }

    // expect first parameter to be a list
    let host = match eval_ast(env, &tokens[0])?.to_value(env)? {
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

    let mut variables = Map::with_type_and_capacity(KeyKind::String, 1);

    let mut found = false;
    match host {
        Value::List(list) => {
            for item in list.iter() {
                variables.insert(key.clone(), item.clone())?;
                let mut env = env.child();
                env.set_variables(&variables);
                match eval_ast(&env, lambda)?.to_value(&env)? {
                    Value::Bool(b) => {
                        if b {
                            if found {
                                found = false;
                                break;
                            }
                            found = true;
                        }
                    }
                    _ => miette::bail!("Invalid type for exists_one: {:?}", lambda),
                }
            }
        }
        Value::Map(map) => {
            for (_key, value) in map.iter() {
                variables.insert(key.clone(), value.clone())?;
                let mut env = env.child();
                env.set_variables(&variables);
                match eval_ast(&env, lambda)?.to_value(&env)? {
                    Value::Bool(b) => {
                        if b {
                            if found {
                                found = false;
                                break;
                            }
                            found = true;
                        }
                    }
                    _ => miette::bail!("Invalid type for exists_one: {:?}", lambda),
                }
            }
        }
        _ => unreachable!(),
    }

    Ok(Value::Bool(found))
}

pub fn map(env: &Environment, tokens: &[TokenTree]) -> Result<Value, Error> {
    if tokens.len() != 3 && tokens.len() != 4 {
        miette::bail!("expected 3 or 4 arguments, found {}", tokens.len());
    }

    let this = if tokens.len() == 3 {
        match eval_ast(env, &tokens[0])?.to_value(env)? {
            v if matches!(v, Value::List(_) | Value::Map(_)) => v,
            _ => miette::bail!("Invalid type for map: {:?}", tokens[0]),
        }
    } else {
        filter(env, &tokens[0..3])?
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
                return Ok(Value::List(list));
            }
            let mut new_list =
                List::with_type_and_capacity(list.element_type().unwrap(), list.len());

            let mut variables = Map::with_type_and_capacity(KeyKind::String, 1);
            for item in list.iter() {
                variables.insert(key.clone(), item.clone())?;
                let mut env = env.child();
                env.set_variables(&variables);
                new_list.push(eval_ast(&env, lambda)?.to_value(&env)?)?;
            }
            Ok(Value::List(new_list))
        }
        Value::Map(map) => {
            if map.is_empty() {
                return Ok(Value::Map(map));
            }
            let mut new_map = Map::with_capacity(map.len());
            let mut variables = Map::with_type_and_capacity(KeyKind::String, 1);
            for (k, value) in map.iter() {
                variables.insert(key.clone(), value.clone())?;

                let mut env = env.child();
                env.set_variables(&variables);
                new_map.insert(k.clone(), eval_ast(&env, lambda)?.to_value(&env)?)?;
            }
            Ok(Value::Map(new_map))
        }
        _ => unreachable!(),
    }
}

pub fn filter(env: &Environment, tokens: &[TokenTree]) -> Result<Value, Error> {
    if tokens.len() != 3 {
        miette::bail!("expected 2 arguments, found {}", tokens.len());
    }
    let host = match eval_ast(env, &tokens[0])?.to_value(env)? {
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

    let mut variables = Map::with_type_and_capacity(KeyKind::String, 1);

    match host {
        Value::List(list) => {
            let mut new_list =
                List::with_type_and_capacity(list.element_type().unwrap(), list.len());
            for item in list.iter() {
                variables.insert(key.clone(), item.clone())?;
                let mut env = env.child();
                env.set_variables(&variables);
                match eval_ast(&env, lambda)?.to_value(&env)? {
                    Value::Bool(b) => {
                        if b {
                            new_list.push(item.clone())?;
                        }
                    }
                    _ => miette::bail!("Invalid type for filter: {:?}", lambda),
                }
            }
            Ok(Value::List(new_list))
        }
        Value::Map(map) => {
            let mut new_map = Map::with_capacity(map.len());
            for (k, v) in map.iter() {
                variables.insert(key.clone(), v.clone())?;
                let mut env = env.child();
                env.set_variables(&variables);
                match eval_ast(&env, lambda)?.to_value(&env)? {
                    Value::Bool(b) => {
                        if b {
                            new_map.insert(k.clone(), v.clone())?;
                        }
                    }
                    _ => miette::bail!("Invalid type for filter: {:?}", lambda),
                }
            }
            Ok(Value::Map(new_map))
        }
        _ => unreachable!(),
    }
}

pub fn contains(env: &Environment, tokens: &[TokenTree]) -> Result<Value, Error> {
    if tokens.len() != 2 {
        miette::bail!("expected 2 arguments, found {}", tokens.len());
    }

    let s = match eval_ast(env, &tokens[0])?.to_value(env)? {
        Value::String(s) => s,
        _ => miette::bail!("Invalid type for contains: {:?}", tokens[0]),
    };

    let value = match eval_ast(env, &tokens[1])?.to_value(env)? {
        Value::String(s) => s,
        _ => miette::bail!("Invalid type for contains: {:?}", tokens[1]),
    };

    Ok(Value::Bool(s.contains(&*value)))
}

pub fn starts_with(env: &Environment, tokens: &[TokenTree]) -> Result<Value, Error> {
    if tokens.len() != 2 {
        miette::bail!("expected 2 arguments, found {}", tokens.len());
    }

    let s = match eval_ast(env, &tokens[0])?.to_value(env)? {
        Value::String(s) => s,
        _ => miette::bail!("Invalid type for starts_with: {:?}", tokens[0]),
    };

    let value = match eval_ast(env, &tokens[1])?.to_value(env)? {
        Value::String(s) => s,
        _ => miette::bail!("Invalid type for starts_with: {:?}", tokens[1]),
    };

    Ok(Value::Bool(s.starts_with(&*value)))
}

pub fn matches(env: &Environment, tokens: &[TokenTree]) -> Result<Value, Error> {
    if tokens.len() != 2 {
        miette::bail!("expected 2 arguments, found {}", tokens.len());
    }

    let s = match eval_ast(env, &tokens[0])?.to_value(env)? {
        Value::String(s) => s,
        _ => miette::bail!("Invalid type for matches: {:?}", tokens[0]),
    };

    let value = match eval_ast(env, &tokens[1])?.to_value(env)? {
        Value::String(s) => s,
        _ => miette::bail!("Invalid type for matches: {:?}", tokens[1]),
    };

    let re = Regex::new(&value);

    match re {
        Ok(re) => Ok(Value::Bool(re.is_match(&s))),
        Err(e) => miette::bail!("Invalid regex: {}", e),
    }
}

pub fn uint(env: &Environment, tokens: &[TokenTree]) -> Result<Value, Error> {
    if tokens.len() != 1 {
        miette::bail!("expected 1 argument, found {}", tokens.len());
    }

    let v = match eval_ast(env, &tokens[0])?.to_value(env)? {
        Value::Int(i) => Value::Uint(i as u64),
        Value::Uint(u) => Value::Uint(u),
        Value::Double(d) => Value::Uint(d as u64),
        Value::String(s) => match s.parse::<u64>() {
            Ok(u) => Value::Uint(u),
            Err(_) => miette::bail!("Invalid type for uint: {:?}", tokens[0]),
        },
        _ => miette::bail!("Invalid type for uint: {:?}", tokens[0]),
    };

    Ok(v)
}

pub fn int(env: &Environment, tokens: &[TokenTree]) -> Result<Value, Error> {
    if tokens.len() != 1 {
        miette::bail!("expected 1 argument, found {}", tokens.len());
    }

    let v = match eval_ast(env, &tokens[0])?.to_value(env)? {
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

pub fn string(env: &Environment, tokens: &[TokenTree]) -> Result<Value, Error> {
    if tokens.len() != 1 {
        miette::bail!("expected 1 argument, found {}", tokens.len());
    }

    let v = match eval_ast(env, &tokens[0])?.to_value(env)? {
        Value::Int(i) => i.to_string().into(),
        Value::Uint(u) => u.to_string().into(),
        Value::Double(d) => d.to_string().into(),
        Value::String(s) => s.into(),
        Value::Bytes(s) => String::from_utf8_lossy(&s).to_string().into(),
        Value::Bool(b) => b.to_string().into(),
        Value::Null => "null".into(),
        Value::Timestamp(t) => t.to_string().into(),
        Value::Duration(d) => d.to_string().into(),
        _ => miette::bail!("Invalid type for string: {:?}", tokens[0]),
    };

    Ok(v)
}

pub fn timestamp(env: &Environment, tokens: &[TokenTree]) -> Result<Value, Error> {
    if tokens.len() != 1 {
        miette::bail!("expected 1 argument, found {}", tokens.len());
    }

    let v = match eval_ast(env, &tokens[0])?.to_value(env)? {
        Value::String(s) => {
            let t = match OffsetDateTime::parse(&s, &Iso8601::PARSING) {
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

    let v = eval_ast(env, &tokens[0])?.to_value(env)?;

    Ok(v)
}

pub fn duration(env: &Environment, tokens: &[TokenTree]) -> Result<Value, Error> {
    if tokens.len() != 1 {
        miette::bail!("expected 1 argument, found {}", tokens.len());
    }

    let v = match eval_ast(env, &tokens[0])?.to_value(env)? {
        Value::String(s) => {
            let mut result = Duration::ZERO;
            let mut acc = 0i64;
            let mut chars = s.chars().peekable();
            while let Some(c) = chars.next() {
                match c {
                    c if c.is_ascii_digit() => {
                        let d = c.to_digit(10).unwrap() as i64;
                        acc *= 10 + d;
                        continue;
                    }
                    'd' => {
                        result += Duration::days(acc);
                        acc = 0;
                    }
                    'h' => {
                        result += Duration::hours(acc);
                        acc = 0;
                    }
                    'm' => {
                        if chars.peek() == Some(&'s') {
                            result += Duration::milliseconds(acc);
                            chars.next();
                            acc = 0;
                        } else {
                            result += Duration::minutes(acc);
                            acc = 0;
                        }
                    }
                    's' => {
                        result += Duration::seconds(acc);
                        acc = 0;
                    }
                    'n' => {
                        if chars.peek() == Some(&'s') {
                            result += Duration::nanoseconds(acc);
                            chars.next();
                            acc = 0;
                        } else {
                            miette::bail!("Invalid type for duration: {:?}", tokens[0]);
                        }
                    }
                    _ => miette::bail!("Invalid type for duration: {:?}", tokens[0]),
                }
            }

            if acc != 0 {
                miette::bail!("Invalid type for duration: {:?}", tokens[0]);
            }

            if result == Duration::ZERO {
                miette::bail!("Invalid type for duration: {:?}", tokens[0]);
            }

            Value::Duration(result)
        }
        _ => miette::bail!("Invalid type for duration: {:?}", tokens[0]),
    };

    Ok(v)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{EnvironmentBuilder, Function, Parser};

    fn is_function(_: Function) {}

    #[test]
    fn implement_functions() {
        is_function(Box::new(size));
        is_function(Box::new(type_fn));
        is_function(Box::new(has));
        is_function(Box::new(all));
        is_function(Box::new(exists));
        is_function(Box::new(exists_one));
        is_function(Box::new(map));
        is_function(Box::new(filter));
        is_function(Box::new(contains));
        is_function(Box::new(starts_with));
        is_function(Box::new(matches));
        is_function(Box::new(uint));
        is_function(Box::new(int));
        is_function(Box::new(string));
        is_function(Box::new(dyn_fn));
        is_function(Box::new(duration));
        is_function(Box::new(timestamp));
    }

    #[test]
    fn test_size_primitive() {
        let env = EnvironmentBuilder::default();
        let env = env.to_sealed();

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
        let env = env.to_sealed();

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
        let env = env.to_sealed();
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

        let env = env.to_sealed();
        let result = all(&env, &[TokenTree::Atom(Atom::Ident("list")), ident, lambda]);
        assert!(result.is_ok(), "expected ok got err: result={:?}", result);
        assert_eq!(result.unwrap(), Value::Bool(true));

        let lambda = Parser::new("x > 1").parse().unwrap();
        let ident = TokenTree::Atom(Atom::Ident("x"));
        let result = all(&env, &[TokenTree::Atom(Atom::Ident("list")), ident, lambda]);
        assert!(result.is_ok(), "expected ok got err: result={:?}", result);
        assert_eq!(result.unwrap(), Value::Bool(false));

        let lambda = Parser::new("y > 1").parse().unwrap();
        let ident = TokenTree::Atom(Atom::Ident("x"));
        let result = all(&env, &[TokenTree::Atom(Atom::Ident("list")), ident, lambda]);
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
        let lambda = Parser::new("x > 0").parse().unwrap();

        let env = env.to_sealed();
        let result = all(&env, &[TokenTree::Atom(Atom::Ident("m")), ident, lambda]);
        assert!(result.is_ok(), "expected ok got err: result={:?}", result);
        assert_eq!(result.unwrap(), Value::Bool(true));

        let ident = TokenTree::Atom(Atom::Ident("x"));
        let lambda = Parser::new("x > 1").parse().unwrap();
        let result = all(&env, &[TokenTree::Atom(Atom::Ident("m")), ident, lambda]);
        assert!(result.is_ok(), "expected ok got err: result={:?}", result);
        assert_eq!(result.unwrap(), Value::Bool(false));

        let ident = TokenTree::Atom(Atom::Ident("x"));
        let lambda = Parser::new("y > 1").parse().unwrap();
        let result = all(&env, &[TokenTree::Atom(Atom::Ident("m")), ident, lambda]);
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

        let env = env.to_sealed();
        let result = exists(&env, &[TokenTree::Atom(Atom::Ident("list")), ident, lambda]);
        assert!(result.is_ok(), "expected ok got err: result={:?}", result);
        assert_eq!(result.unwrap(), Value::Bool(true));

        let ident = TokenTree::Atom(Atom::Ident("x"));
        let lambda = Parser::new("x > 3").parse().unwrap();
        let result = exists(&env, &[TokenTree::Atom(Atom::Ident("list")), ident, lambda]);
        assert!(result.is_ok(), "expected ok got err: result={:?}", result);
        assert_eq!(result.unwrap(), Value::Bool(false));

        let ident = TokenTree::Atom(Atom::Ident("x"));
        let lambda = Parser::new("y > 1").parse().unwrap();
        let result = exists(&env, &[TokenTree::Atom(Atom::Ident("list")), ident, lambda]);
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
        let lambda = Parser::new("x > 2").parse().unwrap();

        let env = env.to_sealed();
        let result = exists(&env, &[TokenTree::Atom(Atom::Ident("m")), ident, lambda]);
        assert!(result.is_ok(), "expected ok got err: result={:?}", result);
        assert_eq!(result.unwrap(), Value::Bool(true));

        let ident = TokenTree::Atom(Atom::Ident("x"));
        let lambda = Parser::new("x > 3").parse().unwrap();
        let result = exists(&env, &[TokenTree::Atom(Atom::Ident("m")), ident, lambda]);
        assert!(result.is_ok(), "expected ok got err: result={:?}", result);
        assert_eq!(result.unwrap(), Value::Bool(false));

        let ident = TokenTree::Atom(Atom::Ident("x"));
        let lambda = Parser::new("y > 1").parse().unwrap();
        let result = exists(&env, &[TokenTree::Atom(Atom::Ident("m")), ident, lambda]);
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

        let env = env.to_sealed();
        let result = exists_one(&env, &[TokenTree::Atom(Atom::Ident("list")), ident, lambda]);
        assert!(result.is_ok(), "expected ok got err: result={:?}", result);
        assert_eq!(result.unwrap(), Value::Bool(true));

        let ident = TokenTree::Atom(Atom::Ident("x"));
        let lambda = Parser::new("x > 3").parse().unwrap();
        let result = exists_one(&env, &[TokenTree::Atom(Atom::Ident("list")), ident, lambda]);
        assert!(result.is_ok(), "expected ok got err: result={:?}", result);
        assert_eq!(result.unwrap(), Value::Bool(false));

        let ident = TokenTree::Atom(Atom::Ident("x"));
        let lambda = Parser::new("y > 1").parse().unwrap();
        let result = exists_one(&env, &[TokenTree::Atom(Atom::Ident("list")), ident, lambda]);
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
        let lambda = Parser::new("x > 2").parse().unwrap();

        let env = env.to_sealed();
        let result = exists_one(&env, &[TokenTree::Atom(Atom::Ident("m")), ident, lambda]);
        assert!(result.is_ok(), "expected ok got err: result={:?}", result);
        assert_eq!(result.unwrap(), Value::Bool(true));

        let ident = TokenTree::Atom(Atom::Ident("x"));
        let lambda = Parser::new("x > 3").parse().unwrap();
        let result = exists_one(&env, &[TokenTree::Atom(Atom::Ident("m")), ident, lambda]);
        assert!(result.is_ok(), "expected ok got err: result={:?}", result);
        assert_eq!(result.unwrap(), Value::Bool(false));

        let ident = TokenTree::Atom(Atom::Ident("x"));
        let lambda = Parser::new("y > 1").parse().unwrap();
        let result = exists_one(&env, &[TokenTree::Atom(Atom::Ident("m")), ident, lambda]);
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

        let env = env.to_sealed();
        let result = map(&env, &[TokenTree::Atom(Atom::Ident("list")), ident, lambda]);
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
        let lambda = Parser::new("x + 1").parse().unwrap();

        let env = env.to_sealed();
        let result = map(&env, &[TokenTree::Atom(Atom::Ident("m")), ident, lambda]);
        assert!(result.is_ok(), "expected ok got err: result={:?}", result);
        assert_eq!(
            result.unwrap(),
            Value::Map(
                Map::new()
                    .insert(Key::from("a"), Value::Int(2))
                    .unwrap()
                    .insert(Key::from("b"), Value::Int(3))
                    .unwrap()
                    .insert(Key::from("c"), Value::Int(4))
                    .unwrap()
                    .to_owned()
            )
        );
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

        let env = env.to_sealed();
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
        let filter = Parser::new("x > 1").parse().unwrap();
        let lambda = Parser::new("x + 1").parse().unwrap();

        let env = env.to_sealed();
        let result = map(
            &env,
            &[TokenTree::Atom(Atom::Ident("m")), ident, filter, lambda],
        );
        assert!(result.is_ok(), "expected ok got err: result={:?}", result);
        assert_eq!(
            result.unwrap(),
            Value::Map(
                Map::new()
                    .insert(Key::from("b"), Value::Int(3))
                    .unwrap()
                    .insert(Key::from("c"), Value::Int(4))
                    .unwrap()
                    .to_owned()
            )
        );
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

        let env = env.to_sealed();
        let result = filter(&env, &[TokenTree::Atom(Atom::Ident("list")), ident, lambda]);
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
        let lambda = Parser::new("x > 1").parse().unwrap();

        let env = env.to_sealed();
        let result = filter(&env, &[TokenTree::Atom(Atom::Ident("m")), ident, lambda]);
        assert!(result.is_ok(), "expected ok got err: result={:?}", result);
        assert_eq!(
            result.unwrap(),
            Value::Map(
                Map::new()
                    .insert(Key::from("b"), Value::Int(2))
                    .unwrap()
                    .insert(Key::from("c"), Value::Int(3))
                    .unwrap()
                    .to_owned()
            )
        );
    }
}
