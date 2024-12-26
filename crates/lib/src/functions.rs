use crate::{
    eval_ast,
    parser::{Atom, Op, TokenTree},
    types::{List, Map},
    Environment, Key, KeyType, Value,
};
use miette::Error;

/// Returns the size of a value.
/// This is an implementation of https://github.com/google/cel-spec/blob/master/doc/langdef.md#functions
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

    let v = match eval_ast(env, &tokens[0])?.to_value(env)?.downcast() {
        Value::Int(_) => Value::String("int".to_string()),
        Value::Uint(_) => Value::String("uint".to_string()),
        Value::Double(_) => Value::String("double".to_string()),
        Value::String(_) => Value::String("string".to_string()),
        Value::Bool(_) => Value::String("bool".to_string()),
        Value::Map(_) => Value::String("map".to_string()),
        Value::List(_) => Value::String("list".to_string()),
        Value::Bytes(_) => Value::String("bytes".to_string()),
        Value::Null => Value::String("null".to_string()),
        Value::Any(_) => unreachable!(),
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
                    let key = Key::String(ident.to_string());
                    Ok(Value::Bool(map.contains_key(&key)?))
                }
                TokenTree::Cons(_op, tokens) => {
                    let env = env.child().with_variables(map);
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
    let ident = match &tokens[1] {
        TokenTree::Atom(Atom::Ident(ident)) => ident,
        _ => miette::bail!("Invalid type for all: {:?}", tokens[1]),
    };

    // expect third parameter to be a lambda
    let lambda = &tokens[2];

    let mut env = env.child();
    let key = Key::String(ident.to_string());
    let mut variables = Map::with_type_and_capacity(KeyType::String, 1);

    let mut all = true;

    match host {
        Value::List(list) => {
            for item in list.iter() {
                variables.insert(key.clone(), item.clone())?;
                env.variables = variables.clone();
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
                env.variables = variables.clone();
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
        TokenTree::Atom(Atom::Ident(ident)) => Key::String(ident.to_string()),
        _ => miette::bail!("Invalid type for exists: {:?}", tokens[1]),
    };

    // expect third parameter to be a lambda
    let lambda = &tokens[2];

    let mut env = env.child();
    let mut variables = Map::with_type_and_capacity(KeyType::String, 1);

    let mut exists = false;
    match host {
        Value::List(list) => {
            for item in list.iter() {
                variables.insert(key.clone(), item.clone())?;
                env.variables = variables.clone();
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
                env.variables = variables.clone();
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
    let list = match eval_ast(env, &tokens[0])?.to_value(env)? {
        Value::List(l) => l,
        _ => miette::bail!("Invalid type for exists_one: {:?}", tokens[0]),
    };

    // expect second parameter to be an identifier
    let ident = match &tokens[1] {
        TokenTree::Atom(Atom::Ident(ident)) => ident,
        _ => miette::bail!("Invalid type for exists_one: {:?}", tokens[1]),
    };

    // expect third parameter to be a lambda
    let lambda = &tokens[2];

    let mut env = env.child();
    let key = Key::String(ident.to_string());
    let mut variables = Map::with_type_and_capacity(KeyType::String, 1);

    let mut found = false;
    for item in list.iter() {
        variables.insert(key.clone(), item.clone())?;
        env.variables = variables.clone();
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

    Ok(Value::Bool(found))
}

pub fn map(env: &Environment, tokens: &[TokenTree]) -> Result<Value, Error> {
    if tokens.len() != 3 || tokens.len() != 4 {
        miette::bail!("expected 2 or 3 arguments, found {}", tokens.len());
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
        TokenTree::Atom(Atom::Ident(ident)) => Key::String(ident.to_string()),
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
            let mut env = env.child();
            let mut new_list =
                List::with_type_and_capacity(list.element_type().unwrap(), list.len());

            for item in list.iter() {
                env.variables = Map::with_type_and_capacity(KeyType::String, 1);
                env.variables.insert(key.clone(), item.clone())?;
                new_list.push(eval_ast(&env, lambda)?.to_value(&env)?)?;
            }
            Ok(Value::List(new_list))
        }
        Value::Map(map) => {
            if map.is_empty() {
                return Ok(Value::Map(map));
            }
            let mut env = env.child();
            let mut new_map = Map::with_capacity(map.len());
            for (key, value) in map.iter() {
                env.variables = Map::with_type_and_capacity(KeyType::String, 1);
                env.variables
                    .insert(Key::String("this".to_string()), value.clone())?;
                new_map.insert(key.clone(), eval_ast(&env, lambda)?.to_value(&env)?)?;
            }
            Ok(Value::Map(new_map))
        }
        _ => unreachable!(),
    }
}

pub fn filter(env: &Environment, tokens: &[TokenTree]) -> Result<Value, Error> {
    if tokens.len() != 2 {
        miette::bail!("expected 2 arguments, found {}", tokens.len());
    }
    let host = match eval_ast(env, &tokens[0])?.to_value(env)? {
        v if matches!(v, Value::List(_) | Value::Map(_)) => v,
        _ => miette::bail!("Invalid type for filter: {:?}", tokens[0]),
    };

    // expect second parameter to be an identifier
    let ident = match &tokens[1] {
        TokenTree::Atom(Atom::Ident(ident)) => ident,
        _ => miette::bail!("Invalid type for exists_one: {:?}", tokens[1]),
    };

    // expect third parameter to be a lambda
    let lambda = &tokens[2];

    let mut env = env.child();
    let key = Key::String(ident.to_string());
    let mut variables = Map::with_type_and_capacity(KeyType::String, 1);

    match host {
        Value::List(list) => {
            let mut new_list =
                List::with_type_and_capacity(list.element_type().unwrap(), list.len());
            for item in list.iter() {
                variables.insert(key.clone(), item.clone())?;
                env.variables = variables.clone();
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
            for (key, value) in map.iter() {
                variables.insert(key.clone(), value.clone())?;
                env.variables = variables.clone();
                match eval_ast(&env, lambda)?.to_value(&env)? {
                    Value::Bool(b) => {
                        if b {
                            new_map.insert(key.clone(), value.clone())?;
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Function, Parser};

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
    }

    #[test]
    fn test_size_primitive() {
        let env = crate::Environment::default();

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
        let env = crate::Environment::default();

        for tt in [
            ("1", Value::String("int".to_string())),
            ("1u", Value::String("uint".to_string())),
            ("1.0", Value::String("double".to_string())),
            ("true", Value::String("bool".to_string())),
            ("'hello'", Value::String("string".to_string())),
            ("null", Value::String("null".to_string())),
            ("[1, 2, 3]", Value::String("list".to_string())),
            ("{'a': 1, 'b': 2}", Value::String("map".to_string())),
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
        let mut env = crate::Environment::default();
        env.set_variable(
            "a",
            Value::Map(
                Map::new()
                    .insert(
                        Key::Int(0),
                        Value::Map(
                            Map::new()
                                .insert(Key::String("b".to_string()), Value::Int(1))
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
        let mut env = crate::Environment::default();
        env.set_variable(
            "list",
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
        let mut env = crate::Environment::default();
        env.set_variable(
            "m",
            Value::Map(
                Map::new()
                    .insert(Key::String("a".to_string()), Value::Int(1))
                    .unwrap()
                    .insert(Key::String("b".to_string()), Value::Int(2))
                    .unwrap()
                    .insert(Key::String("c".to_string()), Value::Int(3))
                    .unwrap()
                    .to_owned(),
            )
            .to_owned(),
        )
        .unwrap();

        let ident = TokenTree::Atom(Atom::Ident("x"));
        let lambda = Parser::new("x > 0").parse().unwrap();

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
        let mut env = crate::Environment::default();
        env.set_variable(
            "list",
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
        let mut env = crate::Environment::default();
        env.set_variable(
            "m",
            Value::Map(
                Map::new()
                    .insert(Key::String("a".to_string()), Value::Int(1))
                    .unwrap()
                    .insert(Key::String("b".to_string()), Value::Int(2))
                    .unwrap()
                    .insert(Key::String("c".to_string()), Value::Int(3))
                    .unwrap()
                    .to_owned(),
            )
            .to_owned(),
        )
        .unwrap();

        let ident = TokenTree::Atom(Atom::Ident("x"));
        let lambda = Parser::new("x > 2").parse().unwrap();

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
}
