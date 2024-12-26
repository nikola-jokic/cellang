use crate::{
    eval_ast,
    parser::{Atom, Op, TokenTree},
    types::Map,
    Environment, Key, KeyType, Value,
};
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

    let v = match eval_ast(env, &vals[0])?.to_value(env)?.downcast() {
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

pub fn has(env: &Environment, vals: &[TokenTree]) -> Result<Value, Error> {
    if vals.len() != 1 {
        miette::bail!("expected 1 argument, found {}", vals.len());
    }

    match &vals[0] {
        TokenTree::Cons(op, tokens) if matches!(op, Op::Field | Op::Index) => {
            let map = match eval_ast(env, &tokens[0])?.to_value(env)? {
                Value::Map(m) => m,
                _ => miette::bail!("Invalid type for has: {:?}", vals[0]),
            };

            match &tokens[1] {
                TokenTree::Atom(Atom::Ident(ident)) => {
                    if !matches!(*op, Op::Field) {
                        miette::bail!("Invalid type for has: {:?}", vals[0]);
                    }
                    let key = Key::String(ident.to_string());
                    Ok(Value::Bool(map.contains_key(&key)?))
                }
                TokenTree::Cons(_op, tokens) => {
                    let env = env.new_child().with_variables(map);
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
    let list = match eval_ast(env, &tokens[0])?.to_value(env)? {
        Value::List(l) => l,
        _ => miette::bail!("Invalid type for all: {:?}", tokens[0]),
    };

    // expect second parameter to be an identifier
    let ident = match &tokens[1] {
        TokenTree::Atom(Atom::Ident(ident)) => ident,
        _ => miette::bail!("Invalid type for all: {:?}", tokens[1]),
    };

    // expect third parameter to be a lambda
    let lambda = &tokens[2];

    let mut env = env.new_child();
    let key = Key::String(ident.to_string());
    let mut variables = Map::with_type_and_capacity(KeyType::String, 1);

    let mut all = true;
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

    Ok(Value::Bool(all))
}

pub fn exists(env: &Environment, tokens: &[TokenTree]) -> Result<Value, Error> {
    if tokens.len() != 3 {
        miette::bail!("expected 3 arguments, found {}", tokens.len());
    }

    // expect first parameter to be a list
    let list = match eval_ast(env, &tokens[0])?.to_value(env)? {
        Value::List(l) => l,
        _ => miette::bail!("Invalid type for exists: {:?}", tokens[0]),
    };

    // expect second parameter to be an identifier
    let ident = match &tokens[1] {
        TokenTree::Atom(Atom::Ident(ident)) => ident,
        _ => miette::bail!("Invalid type for exists: {:?}", tokens[1]),
    };

    // expect third parameter to be a lambda
    let lambda = &tokens[2];

    let mut env = env.new_child();
    let key = Key::String(ident.to_string());
    let mut variables = Map::with_type_and_capacity(KeyType::String, 1);

    let mut exists = false;
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

    let mut env = env.new_child();
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Parser;

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
}
