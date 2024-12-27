use crate::{
    environment::Environment,
    parser::{Atom, Op, TokenTree},
    types::{Key, KeyKind, Map, Value},
    List, Parser,
};
use miette::Error;
use std::collections::HashMap;

/// Evaluate the given program in the given environment.
/// The program is a string representation of the program.
pub fn eval(env: &Environment, program: &str) -> Result<Value, Error> {
    let tree = Parser::new(program).parse()?;
    match eval_ast(env, &tree) {
        Ok(Object::Value(val)) => Ok(val),
        Ok(Object::Ident(ident)) => {
            let key = Key::from(ident);
            if let Some(val) = env.lookup_variable(&key) {
                Ok(val.clone())
            } else {
                miette::bail!("Variable not found: {}", key);
            }
        }
        Err(e) => Err(e),
    }
}

/// Evaluate the given AST in the given environment.
/// The AST is a token tree representation of the program or a subprogram.
pub fn eval_ast(env: &Environment, root: &TokenTree) -> Result<Object, Error> {
    match root {
        TokenTree::Atom(atom) => eval_atom(atom),
        TokenTree::Cons(op, tokens) => Ok(Object::Value(eval_cons(env, op, tokens)?)),
        TokenTree::Call { func, args } => {
            let f = match eval_ast(env, func)? {
                Object::Ident(name) => match env.lookup_function(&name) {
                    Some(f) => f,
                    None => miette::bail!("Function not found: {}", name),
                },
                _ => miette::bail!("Expected function name, found {:?}", func),
            };

            Ok(Object::Value(f(env, args.as_ref())?))
        }
    }
}

/// Evaluate the given atom in the given environment and returns an Object.
/// If the atom is a value, it returns Object::Value.
/// If the atom is an identifier, it returns Object::Ident. Identifier should
/// be resolved by the caller based on the context in which it is used.
/// For example, identifier for a `Op::Call` should be resolved to a function.
/// For the rest of the operations, it should be resolved to a variable.
pub fn eval_atom(atom: &Atom) -> Result<Object, Error> {
    let val = match atom {
        Atom::Int(n) => Object::Value(Value::Int(*n)),
        Atom::Uint(n) => Object::Value(Value::Uint(*n)),
        Atom::Double(n) => Object::Value(Value::Double(*n)),
        Atom::String(s) => Object::Value(s.to_string().into()),
        Atom::Bool(b) => Object::Value(Value::Bool(*b)),
        Atom::Null => Object::Value(Value::Null),
        Atom::Bytes(b) => Object::Value(Value::Bytes(b.clone().to_vec())),
        Atom::Ident(ident) => Object::Ident(ident.to_string()),
    };
    Ok(val)
}

/// Evaluate the given cons in the given environment.
/// The cons is a list of tokens with an operator.
/// The operator is used to determine the operation to be performed.
pub fn eval_cons(env: &Environment, op: &Op, tokens: &[TokenTree]) -> Result<Value, Error> {
    let val = match op {
        Op::Call => panic!("Call should be handled in eval_ast"),
        Op::Field => {
            assert!(tokens.len() == 2);

            let map = match eval_ast(env, &tokens[0])?.to_value(env)? {
                Value::Map(map) => map,
                _ => miette::bail!("Expected reference to a map, found {:?}", tokens[0]),
            };

            let mut env = env.child();
            env.set_variables(&map);

            eval_ast(&env, &tokens[1])?.to_value(&env)?
        }
        Op::Index => {
            assert!(tokens.len() == 2);

            match eval_ast(env, &tokens[0])?.to_value(env)? {
                Value::List(list) => {
                    let i = match eval_ast(env, &tokens[1])?.to_value(env)? {
                        Value::Int(n) => n,
                        _ => miette::bail!("Expected int index, found {:?}", tokens[1]),
                    };

                    if i < 0 || i >= list.len() as i64 {
                        miette::bail!("Index out of bounds: {}", i);
                    }

                    list.get(i as usize).unwrap().clone()
                }

                Value::Map(map) => {
                    let key = Key::try_from(eval_ast(env, &tokens[1])?.to_value(env)?)?;

                    if let Some(val) = map.get(&key)? {
                        val.clone()
                    } else {
                        miette::bail!("Key not found: {}", key);
                    }
                }
                _ => miette::bail!("Expected reference to a list or map, found {:?}", tokens[0]),
            }
        }
        Op::Not => {
            let lhs = eval_ast(env, &tokens[0])?.to_value(env)?;
            match lhs {
                Value::Bool(b) => Value::Bool(!b),
                _ => miette::bail!("Expected bool, found {:?}", tokens[0]),
            }
        }
        Op::Plus => {
            let lhs = eval_ast(env, &tokens[0])?.to_value(env)?;
            let rhs = eval_ast(env, &tokens[1])?.to_value(env)?;
            lhs.plus(&rhs)?
        }
        Op::Minus => {
            let lhs = eval_ast(env, &tokens[0])?.to_value(env)?;
            match tokens.len() {
                1 => match lhs {
                    Value::Int(n) => Value::Int(-n),
                    Value::Double(n) => Value::Double(-n),
                    _ => miette::bail!("Expected number, found {:?}", tokens[0]),
                },
                2 => {
                    let rhs = eval_ast(env, &tokens[1])?.to_value(env)?;
                    lhs.minus(&rhs)?
                }
                _ => miette::bail!("Expected 1 or 2 arguments, found {}", tokens.len()),
            }
        }
        Op::Multiply => {
            let lhs = eval_ast(env, &tokens[0])?.to_value(env)?;
            let rhs = eval_ast(env, &tokens[1])?.to_value(env)?;
            lhs.multiply(&rhs)?
        }
        Op::Devide => {
            let lhs = eval_ast(env, &tokens[0])?.to_value(env)?;
            let rhs = eval_ast(env, &tokens[1])?.to_value(env)?;
            lhs.devide(&rhs)?
        }
        Op::Mod => {
            let lhs = eval_ast(env, &tokens[0])?.to_value(env)?;
            let rhs = eval_ast(env, &tokens[1])?.to_value(env)?;
            lhs.reminder(&rhs)?
        }
        Op::And => {
            let lhs = eval_ast(env, &tokens[0])
                .unwrap_or(Object::Value(Value::Bool(false)))
                .to_value(env)
                .unwrap_or(Value::Bool(false));

            if lhs == Value::Bool(false) {
                return Ok(Value::Bool(false));
            }

            eval_ast(env, &tokens[1])
                .unwrap_or(Object::Value(Value::Bool(false)))
                .to_value(env)
                .unwrap_or(Value::Bool(false))
        }
        Op::Or => {
            assert!(tokens.len() == 2);

            let lhs = eval_ast(env, &tokens[0])
                .unwrap_or(Object::Value(Value::Bool(false)))
                .to_value(env)
                .unwrap_or(Value::Bool(false));

            if lhs == Value::Bool(true) {
                return Ok(Value::Bool(true));
            }

            eval_ast(env, &tokens[1])
                .unwrap_or(Object::Value(Value::Bool(false)))
                .to_value(env)
                .unwrap_or(Value::Bool(false))
        }
        Op::NotEqual => {
            let lhs = eval_ast(env, &tokens[0])?.to_value(env)?;
            let rhs = eval_ast(env, &tokens[1])?.to_value(env)?;
            lhs.not_equal(&rhs)?
        }
        Op::EqualEqual => {
            assert!(tokens.len() == 2);
            let lhs = eval_ast(env, &tokens[0])?.to_value(env)?;
            let rhs = eval_ast(env, &tokens[1])?.to_value(env)?;
            lhs.equal(&rhs)?
        }
        Op::Greater => {
            let lhs = eval_ast(env, &tokens[0])?.to_value(env)?;
            let rhs = eval_ast(env, &tokens[1])?.to_value(env)?;
            lhs.greater(&rhs)?
        }
        Op::GreaterEqual => {
            let lhs = eval_ast(env, &tokens[0])?.to_value(env)?;
            let rhs = eval_ast(env, &tokens[1])?.to_value(env)?;
            lhs.greater_equal(&rhs)?
        }
        Op::Less => {
            let lhs = eval_ast(env, &tokens[0])?.to_value(env)?;
            let rhs = eval_ast(env, &tokens[1])?.to_value(env)?;
            lhs.less(&rhs)?
        }
        Op::LessEqual => {
            let lhs = eval_ast(env, &tokens[0])?.to_value(env)?;
            let rhs = eval_ast(env, &tokens[1])?.to_value(env)?;
            lhs.less_equal(&rhs)?
        }
        Op::List => {
            if tokens.is_empty() {
                return Ok(Value::List(List::new()));
            }

            let mut list = Vec::with_capacity(tokens.len());
            let mut iter = tokens.iter();
            let first = eval_ast(env, iter.next().unwrap())?.to_value(env)?;
            let kind = first.kind();
            list.push(first);

            for token in iter {
                let value = eval_ast(env, token)?.to_value(env)?;
                if value.kind() != kind {
                    miette::bail!("List elements must have the same type");
                }
                list.push(value);
            }

            Value::List(list.into())
        }
        Op::Map => {
            if tokens.is_empty() {
                return Ok(Value::Map(Map::new()));
            }

            let mut iter = tokens.iter();
            let first_key =
                eval_ast(env, iter.next().expect("Key must be present"))?.to_value(env)?;
            let first_value =
                eval_ast(env, iter.next().expect("Value must be present"))?.to_value(env)?;
            let key_kind = KeyKind::try_from(first_key.kind())?;

            let mut map = HashMap::new();
            map.insert(Key::try_from(first_key)?, first_value);

            while let (Some(key), Some(value)) = (iter.next(), iter.next()) {
                let key = eval_ast(env, key)?.to_value(env)?;
                let value = eval_ast(env, value)?.to_value(env)?;
                let kk = KeyKind::try_from(key.kind())?;
                if kk != key_kind {
                    miette::bail!("Map elements must have the same type");
                }
                map.insert(Key::try_from(key)?, value);
            }

            Value::Map(map.into())
        }
        Op::IfTernary => {
            let lhs = match eval_ast(env, &tokens[0])?.to_value(env)? {
                Value::Bool(b) => b,
                _ => miette::bail!("Expected bool, found {:?}", tokens[0]),
            };

            if lhs {
                eval_ast(env, &tokens[1])?.to_value(env)?
            } else {
                eval_ast(env, &tokens[2])?.to_value(env)?
            }
        }
        Op::Group => eval_ast(env, &tokens[0])?.to_value(env)?,
        Op::In => {
            let lhs = eval_ast(env, &tokens[0])?.to_value(env)?;
            match eval_ast(env, &tokens[1])?.to_value(env)? {
                Value::List(list) => Value::Bool(list.contains(&lhs)?),
                Value::Map(map) => Value::Bool(map.contains_key(&Key::try_from(lhs)?)?),
                _ => miette::bail!("Expected list, found {:?}", tokens[1]),
            }
        }
        Op::For => miette::bail!("For loop is not supported"),
        Op::While => miette::bail!("While loop is not supported"),
        Op::Var => miette::bail!("Var is not supported"),
    };
    Ok(val)
}

/// Object represents a value or an identifier.
/// If the object is an identifier, identifier can either be a variable or a function.
/// Value variant is a primitive value
/// Ident variant is a variable or a function name
///
/// The identifier resolution is done in some context. If it is a function call,
/// then the lookup should be performed in function list.
/// Otherwise, it should be looked up in the variable list.
#[derive(Debug, PartialEq, Clone)]
pub enum Object {
    Value(Value),
    Ident(String),
}

impl Object {
    /// Get the value of the object. If the object is an identifier,
    /// look up the value in the environment.
    /// It always resolves to a variable lookup since function is not a value.
    ///
    /// If the function resolution is needed, it should be done in the caller.
    pub fn to_value(&self, env: &Environment) -> Result<Value, Error> {
        match self {
            Object::Value(value) => Ok(value.clone()),
            Object::Ident(ident) => {
                let ident = Key::from(ident.as_str());
                if let Some(val) = env.lookup_variable(&ident) {
                    Ok(val.clone())
                } else {
                    miette::bail!("Variable not found: {}", ident);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::environment::EnvironmentBuilder;

    #[test]
    fn test_eval_primitives() {
        let env = EnvironmentBuilder::default();
        let env = env.build();
        assert_eq!(eval(&env, "42").expect("42"), Value::Int(42));
        assert_eq!(eval(&env, "true").expect("true"), Value::Bool(true));
        assert_eq!(eval(&env, "false").expect("false"), Value::Bool(false));
        assert_eq!(eval(&env, "null").expect("null"), Value::Null);
        assert_eq!(eval(&env, "\"hello\"").expect("hello"), "hello".into());
    }

    #[test]
    fn test_eval_plus() {
        let env = EnvironmentBuilder::default();
        let env = env.build();
        assert_eq!(eval(&env, "1 + 2").expect("1 + 2"), Value::Int(3));
        assert_eq!(eval(&env, "1u + 2u").expect("1u + 2u"), Value::Uint(3));
        assert_eq!(
            eval(&env, "1.0 + 2.0").expect("1.0 + 2.0"),
            Value::Double(3.0)
        );
        assert_eq!(
            eval(&env, "\"hello\" + \"world\"").expect("\"hello\" + \"world\""),
            "helloworld".into()
        );
    }

    #[test]
    fn test_eval_minus() {
        let env = EnvironmentBuilder::default();
        let env = env.build();
        assert_eq!(eval(&env, "1 - 2").expect("1 - 2"), Value::Int(-1));
        assert_eq!(eval(&env, "2u - 1u").expect("2u - 1u"), Value::Uint(1));
        assert_eq!(
            eval(&env, "1.0 - 2.0").expect("1.0 - 2.0"),
            Value::Double(-1.0)
        );
    }

    #[test]
    fn test_eval_multiply() {
        let env = EnvironmentBuilder::default();
        let env = env.build();
        assert_eq!(eval(&env, "2 * 3").expect("2 * 3"), Value::Int(6));
        assert_eq!(eval(&env, "2u * 3u").expect("2u * 3u"), Value::Uint(6));
        assert_eq!(
            eval(&env, "2.0 * 3.0").expect("2.0 * 3.0"),
            Value::Double(6.0)
        );
    }

    #[test]
    fn test_eval_devide() {
        let env = EnvironmentBuilder::default();
        let env = env.build();
        assert_eq!(eval(&env, "6 / 3").expect("6 / 3"), Value::Int(2));
        assert_eq!(eval(&env, "6u / 3u").expect("6u / 3u"), Value::Uint(2));
        assert_eq!(
            eval(&env, "6.0 / 3.0").expect("6.0 / 3.0"),
            Value::Double(2.0)
        );
    }

    #[test]
    fn test_eval_and() {
        let env = EnvironmentBuilder::default();
        let env = env.build();
        assert_eq!(
            eval(&env, "true && false").expect("true && false"),
            Value::Bool(false)
        );
        assert_eq!(
            eval(&env, "true && true").expect("true && true"),
            Value::Bool(true)
        );
    }

    #[test]
    fn test_eval_or() {
        let env = EnvironmentBuilder::default();
        let env = env.build();
        assert_eq!(
            eval(&env, "false || true").expect("false || true"),
            Value::Bool(true)
        );
        assert_eq!(
            eval(&env, "false || false").expect("false || false"),
            Value::Bool(false)
        );
    }

    #[test]
    fn test_eval_equal_equal() {
        let env = EnvironmentBuilder::default();
        let env = env.build();
        assert_eq!(eval(&env, "1 == 1").expect("1 == 1"), Value::Bool(true));
        assert_eq!(eval(&env, "1 == 2").expect("1 == 2"), Value::Bool(false));
        assert_eq!(eval(&env, "1u == 1u").expect("1u == 1u"), Value::Bool(true));
        assert_eq!(
            eval(&env, "1u == 2u").expect("1u == 2u"),
            Value::Bool(false)
        );
        assert_eq!(
            eval(&env, "1.0 == 1.0").expect("1.0 == 1.0"),
            Value::Bool(true)
        );
        assert_eq!(
            eval(&env, "1.0 == 2.0").expect("1.0 == 2.0"),
            Value::Bool(false)
        );
        assert_eq!(
            eval(&env, "true == true").expect("true == true"),
            Value::Bool(true)
        );
        assert_eq!(
            eval(&env, "true == false").expect("true == false"),
            Value::Bool(false)
        );
        assert_eq!(
            eval(&env, "\"hello\" == \"hello\"").expect("\"hello\" == \"hello\""),
            Value::Bool(true)
        );
        assert_eq!(
            eval(&env, "\"hello\" == \"world\"").expect("\"hello\" == \"world\""),
            Value::Bool(false)
        );
    }

    #[test]
    fn test_not_equal() {
        let env = EnvironmentBuilder::default();
        let env = env.build();
        assert_eq!(eval(&env, "1 != 1").expect("1 != 1"), Value::Bool(false));
        assert_eq!(eval(&env, "1 != 2").expect("1 != 2"), Value::Bool(true));
        assert_eq!(
            eval(&env, "1u != 1u").expect("1u != 1u"),
            Value::Bool(false)
        );
        assert_eq!(eval(&env, "1u != 2u").expect("1u != 2u"), Value::Bool(true));
        assert_eq!(
            eval(&env, "1.0 != 1.0").expect("1.0 != 1.0"),
            Value::Bool(false)
        );
        assert_eq!(
            eval(&env, "1.0 != 2.0").expect("1.0 != 2.0"),
            Value::Bool(true)
        );
        assert_eq!(
            eval(&env, "true != true").expect("true != true"),
            Value::Bool(false)
        );
        assert_eq!(
            eval(&env, "true != false").expect("true != false"),
            Value::Bool(true)
        );
        assert_eq!(
            eval(&env, "\"hello\" != \"hello\"").expect("\"hello\" != \"hello\""),
            Value::Bool(false)
        );
        assert_eq!(
            eval(&env, "\"hello\" != \"world\"").expect("\"hello\" != \"world\""),
            Value::Bool(true)
        );
    }

    #[test]
    fn test_eval_greater() {
        let env = EnvironmentBuilder::default();
        let env = env.build();
        assert_eq!(eval(&env, "2 > 1").expect("2 > 1"), Value::Bool(true));
        assert_eq!(eval(&env, "1 > 2").expect("1 > 2"), Value::Bool(false));
        assert_eq!(eval(&env, "2u > 1u").expect("2u > 1u"), Value::Bool(true));
        assert_eq!(eval(&env, "1u > 2u").expect("1u > 2u"), Value::Bool(false));
        assert_eq!(
            eval(&env, "2.0 > 1.0").expect("2.0 > 1.0"),
            Value::Bool(true)
        );
        assert_eq!(
            eval(&env, "1.0 > 2.0").expect("1.0 > 2.0"),
            Value::Bool(false)
        );
    }

    #[test]
    fn test_eval_greater_equal() {
        let env = EnvironmentBuilder::default();
        let env = env.build();
        assert_eq!(eval(&env, "2 >= 1").expect("2 >= 1"), Value::Bool(true));
        assert_eq!(eval(&env, "1 >= 2").expect("1 >= 2"), Value::Bool(false));
        assert_eq!(eval(&env, "1 >= 1").expect("1 >= 1"), Value::Bool(true));
        assert_eq!(eval(&env, "2u >= 1u").expect("2u >= 1u"), Value::Bool(true));
        assert_eq!(
            eval(&env, "1u >= 2u").expect("1u >= 2u"),
            Value::Bool(false)
        );
        assert_eq!(eval(&env, "1u >= 1u").expect("1u >= 1u"), Value::Bool(true));
        assert_eq!(
            eval(&env, "2.0 >= 1.0").expect("2.0 >= 1.0"),
            Value::Bool(true)
        );
        assert_eq!(
            eval(&env, "1.0 >= 2.0").expect("1.0 >= 2.0"),
            Value::Bool(false)
        );
        assert_eq!(
            eval(&env, "1.0 >= 1.0").expect("1.0 >= 1.0"),
            Value::Bool(true)
        );
    }

    #[test]
    fn test_eval_less() {
        let env = EnvironmentBuilder::default();
        let env = env.build();
        assert_eq!(eval(&env, "1 < 2").expect("1 < 2"), Value::Bool(true));
        assert_eq!(eval(&env, "2 < 1").expect("2 < 1"), Value::Bool(false));
        assert_eq!(eval(&env, "1u < 2u").expect("1u < 2u"), Value::Bool(true));
        assert_eq!(eval(&env, "2u < 1u").expect("2u < 1u"), Value::Bool(false));
        assert_eq!(
            eval(&env, "1.0 < 2.0").expect("1.0 < 2.0"),
            Value::Bool(true)
        );
        assert_eq!(
            eval(&env, "2.0 < 1.0").expect("2.0 < 1.0"),
            Value::Bool(false)
        );
    }

    #[test]
    fn test_eval_less_equal() {
        let env = EnvironmentBuilder::default();
        let env = env.build();
        assert_eq!(eval(&env, "1 <= 2").expect("1 <= 2"), Value::Bool(true));
        assert_eq!(eval(&env, "2 <= 1").expect("2 <= 1"), Value::Bool(false));
        assert_eq!(eval(&env, "1 <= 1").expect("1 <= 1"), Value::Bool(true));
        assert_eq!(eval(&env, "1u <= 2u").expect("1u <= 2u"), Value::Bool(true));
        assert_eq!(
            eval(&env, "2u <= 1u").expect("2u <= 1u"),
            Value::Bool(false)
        );
        assert_eq!(eval(&env, "1u <= 1u").expect("1u <= 1u"), Value::Bool(true));
        assert_eq!(
            eval(&env, "1.0 <= 2.0").expect("1.0 <= 2.0"),
            Value::Bool(true)
        );
        assert_eq!(
            eval(&env, "2.0 <= 1.0").expect("2.0 <= 1.0"),
            Value::Bool(false)
        );
        assert_eq!(
            eval(&env, "1.0 <= 1.0").expect("1.0 <= 1.0"),
            Value::Bool(true)
        );
    }

    #[test]
    fn test_eval_mod() {
        let env = EnvironmentBuilder::default();
        let env = env.build();
        assert_eq!(eval(&env, "5 % 2").expect("5 % 2"), Value::Int(1));
        assert_eq!(eval(&env, "5u % 2u").expect("5u % 2u"), Value::Uint(1));
    }

    #[test]
    fn test_eval_not() {
        let env = EnvironmentBuilder::default();
        let env = env.build();
        assert_eq!(eval(&env, "!true").expect("!true"), Value::Bool(false));
        assert_eq!(eval(&env, "!false").expect("!false"), Value::Bool(true));
    }

    #[test]
    fn test_list() {
        let env = EnvironmentBuilder::default();
        let env = env.build();
        assert_eq!(eval(&env, "[]").expect("[]"), Value::List(List::new()));
        assert_eq!(
            eval(&env, "[1, 2, 3]").expect("[1, 2, 3]"),
            Value::List(vec![Value::Int(1), Value::Int(2), Value::Int(3)].into())
        );
        assert_eq!(
            eval(&env, "[1u, 2u, 3u]").expect("[1u, 2u, 3u]"),
            Value::List(vec![Value::Uint(1), Value::Uint(2), Value::Uint(3)].into())
        );
        assert_eq!(
            eval(&env, "[1.0, 2.0, 3.0]").expect("[1.0, 2.0, 3.0]"),
            Value::List(vec![Value::Double(1.0), Value::Double(2.0), Value::Double(3.0)].into())
        );
        assert_eq!(
            eval(&env, "[\"hello\", \"world\"]").expect("[\"hello\", \"world\"]"),
            Value::List(vec!["hello".into(), Value::String("world".to_string().into())].into())
        );
        assert_eq!(
            eval(&env, "[true, false]").expect("[true, false]"),
            Value::List(vec![Value::Bool(true), Value::Bool(false)].into())
        );

        // list elements must have the same type
        let tt = [
            "[1, 2u, 3]",
            "[1, 2.0, 3]",
            "[1, \"hello\", 3]",
            "[1, true, 3]",
        ];
        for t in tt.iter() {
            let result = eval(&env, t);
            assert!(result.is_err());
        }
    }

    #[test]
    fn test_map() {
        let tt = [
            ("{}", Value::Map(Map::new())),
            ("{1: 2, 3: 4}", {
                let mut map = HashMap::new();
                map.insert(Key::Int(1), Value::Int(2));
                map.insert(Key::Int(3), Value::Int(4));
                Value::Map(map.into())
            }),
            ("{1u: 2u, 3u: 4u}", {
                let mut map = HashMap::new();
                map.insert(Key::Uint(1), Value::Uint(2));
                map.insert(Key::Uint(3), Value::Uint(4));
                Value::Map(map.into())
            }),
            ("{\"hello\": \"world\"}", {
                let mut map = HashMap::new();
                map.insert(Key::from("hello"), Value::from("world"));
                Value::Map(map.into())
            }),
            ("{true: false}", {
                let mut map = HashMap::new();
                map.insert(Key::Bool(true), Value::Bool(false));
                Value::Map(map.into())
            }),
        ];

        let env = EnvironmentBuilder::default();
        let env = env.build();

        for (input, expected) in tt.iter() {
            let result = eval(&env, input).expect(input);
            assert_eq!(result, *expected, "input: {}", input);
        }

        // keys must be of same kind
        let tt = [
            ("{1: 2, 3u: 4}", "Map elements must have the same type"),
            (
                "{1: 2, \"hello\": 4}",
                "Map elements must have the same type",
            ),
            ("{1: 2, true: 4}", "Map elements must have the same type"),
        ];

        for (input, expected) in tt.iter() {
            let result = eval(&env, input);
            assert!(result.is_err());
            assert_eq!(result.unwrap_err().to_string(), *expected);
        }
    }

    #[test]
    fn test_if_ternary() {
        let env = EnvironmentBuilder::default();
        let env = env.build();

        assert_eq!(
            eval(&env, "1 > 2 ? 1 : 2u").expect("1 > 2 ? 1 : 2u"),
            Value::Uint(2)
        );
        assert_eq!(
            eval(&env, "1 < 2 ? 1 : 2u").expect("1 < 2 ? 1 : 2u"),
            Value::Int(1)
        );
    }

    #[test]
    fn test_group() {
        let env = EnvironmentBuilder::default();
        let env = env.build();

        assert_eq!(
            eval(&env, "(1 + 2) * 3").expect("(1 + 2) * 3"),
            Value::Int(9)
        );
    }

    #[test]
    fn test_in() {
        let env = EnvironmentBuilder::default();
        let env = env.build();

        assert_eq!(
            eval(&env, "1 in [1, 2, 3]").expect("1 in [1, 2, 3]"),
            Value::Bool(true)
        );
        assert_eq!(
            eval(&env, "4 in [1, 2, 3]").expect("4 in [1, 2, 3]"),
            Value::Bool(false)
        );
    }

    #[test]
    fn test_variable() {
        let mut env = EnvironmentBuilder::default();
        env.set_variable(Key::from("x"), Value::from(42i64))
            .expect("to set variable");

        let env = env.build();
        assert_eq!(eval(&env, "x").expect("x"), Value::Int(42));
        assert!(eval(&env, "y").is_err());
    }

    #[test]
    fn test_size() {
        let env = EnvironmentBuilder::default();
        let env = env.build();

        assert_eq!(eval(&env, "size(\"\")").expect("size(\"\")"), Value::Int(0));
        assert_eq!(
            eval(&env, "size(\"hello\")").expect("size(\"hello\")"),
            Value::Int(5)
        );
        assert_eq!(eval(&env, "size([])").expect("size([])"), Value::Int(0));
        assert_eq!(
            eval(&env, "size([1, 2, 3])").expect("size([1, 2, 3])"),
            Value::Int(3)
        );
        assert_eq!(eval(&env, "size({})").expect("size({})"), Value::Int(0));
        assert_eq!(
            eval(&env, "size({1: 2, 3: 4})").expect("size({1: 2, 3: 4})"),
            Value::Int(2)
        );
    }

    #[test]
    fn test_method_call() {
        let mut env = EnvironmentBuilder::default();
        env.set_function(
            "foo",
            Box::new(|_env, args: &[TokenTree]| Ok(Value::Int(args.len() as i64))),
        );
        env.set_variable("x".into(), 42i64.into())
            .expect("to set variable");

        let env = env.build();
        assert_eq!(eval(&env, "x.foo()").expect("x.foo()"), Value::Int(1));
    }

    #[test]
    fn test_index_map_access() {
        let mut env = EnvironmentBuilder::default();
        env.set_variable("x".into(), {
            let mut leaf = HashMap::new();
            leaf.insert(Key::from("y"), Value::Int(42));

            let leaf = Value::Map(leaf.into());

            let mut middle_level = HashMap::new();
            middle_level.insert(Key::Int(0), leaf);

            let middle_level = Value::Map(middle_level.into());

            let mut root = HashMap::new();
            root.insert(Key::Bool(true), middle_level);

            Value::Map(root.into())
        })
        .expect("to set variable");

        let env = env.build();
        assert_eq!(
            eval(&env, "x[true][0][\"y\"]").expect("x[true][0][\"y\"]"),
            Value::Int(42)
        );
    }

    #[test]
    fn test_field_map_access() {
        let mut env = EnvironmentBuilder::default();
        env.set_variable("x".into(), {
            let mut leaf = HashMap::new();
            leaf.insert(Key::from("z"), Value::Uint(42));
            let leaf = Value::Map(leaf.into());

            let mut root = HashMap::new();
            root.insert(Key::from("y"), leaf);
            Value::Map(root.into())
        })
        .expect("to set variable");

        let env = env.build();
        assert_eq!(eval(&env, "x.y.z").expect("x.y.z"), Value::Uint(42));
    }

    #[test]
    fn test_basic_zeroish() {
        // https://github.com/google/cel-spec/blob/master/tests/simple/testdata/basic.textproto
        let tt = [
            ("0", 0i64.into()),
            ("0u", 0u64.into()),
            ("0U", 0u64.into()),
            ("0.0", 0.0.into()),
            ("0e+0", 0.0.into()),
            ("\"\"", "".into()),
            ("r\"\"", "".into()),
            ("b\"\"", Value::Bytes(vec![])),
            ("false", false.into()),
            ("null", Value::Null),
            ("{}", Value::Map(Map::new())),
            ("[]", Value::List(List::new())),
            (r#""""""""#, "".into()),
            (r#"''''''"#, "".into()),
        ];

        let env = EnvironmentBuilder::default();
        let env = env.build();
        for (input, expected) in tt {
            let result = eval(&env, input).expect(input);
            assert_eq!(result, expected, "input: {}", input);
        }
    }

    #[test]
    fn test_basic_nonzeroish() {
        // https://github.com/google/cel-spec/blob/master/tests/simple/testdata/basic.textproto
        let tt = [
            ("42", 42i64.into()),
            ("123456789u", 123456789u64.into()),
            ("123456789U", 123456789u64.into()),
            ("-92233720368547758", (-92233720368547758i64).into()),
            ("-2.3e+1", (-23.0).into()),
            ("\"!\"", "!".into()),
            ("'\\''", "'".into()),
            ("b'ÿ'", Value::Bytes("ÿ".as_bytes().to_vec())),
            ("[-1]", Value::List(List::from(vec![Value::Int(-1)]))),
            (r#"{"k":"v"}"#, {
                let mut map = HashMap::new();
                map.insert("k", "v");
                Value::Map(map.into())
            }),
            ("true", true.into()),
            ("0x55555555", 0x55555555i64.into()),
            ("-0x55555555", (-0x55555555i64).into()),
            ("0x55555555u", 0x55555555u64.into()),
            ("0x55555555U", 0x55555555u64.into()),
            (r#""\u270c""#, "\u{270c}".into()),
            (r#""\U0001f431""#, Value::from("\u{1f431}")),
            (
                "\"\\a\\b\\f\\n\\r\\t\\v\\\\\\'\\\"\"",
                "\x07\x08\x0c\n\r\t\x0b\\'\"".into(),
            ),
        ];
        let env = &EnvironmentBuilder::default();
        let env = env.build();
        for (input, expected) in tt {
            let result = eval(&env, input);
            assert!(result.is_ok(), "input: {input}, result: {result:?}");
            assert_eq!(result.unwrap(), expected, "input: {}", input);
        }
    }

    #[test]
    fn test_basic_variables() {
        // https://github.com/google/cel-spec/blob/master/tests/simple/testdata/basic.textproto
        let env = EnvironmentBuilder::default();
        let env = env.build();
        let result = eval(&env, "x");
        assert!(result.is_err(), "Program 'x' failed: {:?}", result);

        let result = eval(&env, "x || true");
        assert!(result.is_ok(), "Program 'x || true' failed: {:?}", result);
        let result = result.unwrap();
        assert_eq!(
            result,
            Value::Bool(true),
            "Program 'x || true' failed: {:?}",
            result
        );
    }

    #[test]
    fn test_basic_functions() {
        // https://github.com/google/cel-spec/blob/master/tests/simple/testdata/basic.textproto
        let env = EnvironmentBuilder::default();
        let env = env.build();
        let result = eval(&env, "1 + 1");
        assert!(result.is_ok(), "Program '1 + 1' failed: {:?}", result);
        let result = result.unwrap();
        assert_eq!(
            result,
            Value::Int(2),
            "Program '1 + 1' failed: {:?}",
            result
        );

        let result = eval(&env, "f_unknown(17)");
        assert!(
            result.is_err(),
            "Program 'f_unknown(17)' failed: {:?}",
            result
        );

        let result = eval(&env, "f_unknown(17) || true");
        assert!(
            result.is_ok(),
            "Program 'f_unknown(17) || true' failed: {:?}",
            result
        );
    }
}
