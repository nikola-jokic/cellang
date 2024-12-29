use crate::{
    environment::Environment,
    parser::{Atom, Op, TokenTree},
    types::{Key, KeyKind, Map, Value},
    Function, List, Parser,
};
use miette::Error;
use std::collections::HashMap;

/// Evaluate the given program in the given environment.
/// The program is a string representation of the program.
pub fn eval(env: &Environment, program: &str) -> Result<Value, Error> {
    let tree = Parser::new(program).parse()?;
    eval_ast(env, &tree)?.to_value()
}

/// Evaluate the given AST in the given environment.
/// The AST is a token tree representation of the program or a subprogram.
pub fn eval_ast<'a>(env: &'a Environment, root: &'a TokenTree) -> Result<Resolver<'a>, Error> {
    match root {
        TokenTree::Atom(atom) => eval_atom(env, atom),
        TokenTree::Cons(op, tokens) => eval_cons(env, op, tokens),
        TokenTree::Call { func, args } => {
            let lhs = eval_ast(env, func)?;
            let f = lhs.try_function()?;
            Ok(Resolver::new(env, Object::Value(f(env, args.as_ref())?)))
        }
    }
}

/// Evaluate the given atom in the given environment and returns an Object.
/// If the atom is a value, it returns Object::Value.
/// If the atom is an identifier, it returns Object::Ident. Identifier should
/// be resolved by the caller based on the context in which it is used.
/// For example, identifier for a `Op::Call` should be resolved to a function.
/// For the rest of the operations, it should be resolved to a variable.
pub fn eval_atom<'a>(env: &'a Environment, atom: &'a Atom) -> Result<Resolver<'a>, Error> {
    let val = match atom {
        Atom::Int(n) => Object::Value(Value::Int(*n)),
        Atom::Uint(n) => Object::Value(Value::Uint(*n)),
        Atom::Double(n) => Object::Value(Value::Double(*n)),
        Atom::String(s) => Object::Value(s.to_string().into()),
        Atom::Bool(b) => Object::Value(Value::Bool(*b)),
        Atom::Null => Object::Value(Value::Null),
        Atom::Bytes(b) => Object::Value(Value::Bytes(b.clone().to_vec())),
        Atom::Ident(ident) => Object::Ident(ident),
    };
    Ok(Resolver::new(env, val))
}

/// Evaluate the given cons in the given environment.
/// The cons is a list of tokens with an operator.
/// The operator is used to determine the operation to be performed.
pub fn eval_cons<'a>(
    env: &'a Environment,
    op: &'a Op,
    tokens: &'a [TokenTree],
) -> Result<Resolver<'a>, Error> {
    let value: Value = match op {
        Op::Call => panic!("Call should be handled in eval_ast"),
        Op::Field => {
            assert!(tokens.len() == 2);

            let lhs = eval_ast(env, &tokens[0])?;
            let m = match lhs.try_value()? {
                Value::Map(map) => map,
                _ => miette::bail!("Expected map, found {:?}", tokens[0]),
            };

            let mut child = env.child();
            child.set_variables(m);
            let result = eval_ast(&child, &tokens[1])?;
            return Ok(Resolver::new(env, Object::Value(result.to_value()?)));
        }
        Op::Index => {
            assert!(tokens.len() == 2);

            match eval_ast(env, &tokens[0])?.try_value()? {
                Value::List(list) => {
                    let i = match eval_ast(env, &tokens[1])?.try_value()? {
                        Value::Int(n) => *n,
                        _ => miette::bail!("Expected int index, found {:?}", tokens[1]),
                    };

                    if i < 0 || i >= list.len() as i64 {
                        miette::bail!("Index out of bounds: {}", i);
                    }

                    list.get(i as usize).unwrap().clone()
                }
                Value::Map(map) => {
                    let key = Key::try_from(eval_ast(env, &tokens[1])?.to_value()?)?;
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
            let lhs = eval_ast(env, &tokens[0])?;
            match lhs.try_value()? {
                Value::Bool(b) => Value::Bool(!b),
                _ => miette::bail!("Expected bool, found {:?}", tokens[0]),
            }
        }
        Op::Plus => {
            let lhs = eval_ast(env, &tokens[0])?;
            let lhs = lhs.try_value()?;
            let rhs = eval_ast(env, &tokens[1])?;
            let rhs = rhs.try_value()?;
            lhs.plus(rhs)?
        }
        Op::Minus => match tokens.len() {
            1 => match eval_ast(env, &tokens[0])?.try_value()? {
                Value::Int(n) => Value::Int(-n),
                Value::Double(n) => Value::Double(-n),
                _ => miette::bail!("Expected number, found {:?}", tokens[0]),
            },
            2 => {
                let lhs = eval_ast(env, &tokens[0])?;
                let lhs = lhs.try_value()?;
                let rhs = eval_ast(env, &tokens[1])?;
                let rhs = rhs.try_value()?;
                lhs.minus(rhs)?
            }
            _ => miette::bail!("Expected 1 or 2 arguments, found {}", tokens.len()),
        },
        Op::Multiply => {
            let lhs = eval_ast(env, &tokens[0])?;
            let lhs = lhs.try_value()?;
            let rhs = eval_ast(env, &tokens[1])?;
            let rhs = rhs.try_value()?;
            lhs.multiply(rhs)?
        }
        Op::Devide => {
            let lhs = eval_ast(env, &tokens[0])?;
            let lhs = lhs.try_value()?;
            let rhs = eval_ast(env, &tokens[1])?;
            let rhs = rhs.try_value()?;
            lhs.devide(rhs)?
        }
        Op::Mod => {
            let lhs = eval_ast(env, &tokens[0])?;
            let lhs = lhs.try_value()?;
            let rhs = eval_ast(env, &tokens[1])?;
            let rhs = rhs.try_value()?;
            lhs.reminder(rhs)?
        }
        Op::And => {
            let lhs = eval_ast(env, &tokens[0])
                .unwrap_or(Resolver::new(env, Object::Value(Value::Bool(false))));
            let lhs = lhs.try_value()?;

            if matches!(lhs, Value::Bool(false)) {
                return Ok(Resolver::new(env, Object::Value(Value::Bool(false))));
            }

            let rhs = eval_ast(env, &tokens[1])?;
            let rhs = rhs.try_value()?;
            match rhs {
                Value::Bool(b) => Value::Bool(*b),
                _ => miette::bail!("Expected bool, found {:?}", tokens[1]),
            }
        }
        Op::Or => {
            assert!(tokens.len() == 2);

            let lhs = eval_ast(env, &tokens[0])
                .unwrap_or(Resolver::new(env, Object::Value(Value::Bool(false))));
            let lhs = lhs.try_value().unwrap_or(&Value::Bool(false));

            if matches!(lhs, Value::Bool(true)) {
                return Ok(Resolver::new(env, Object::Value(Value::Bool(true))));
            }

            let rhs = eval_ast(env, &tokens[1])?;
            let rhs = rhs.try_value()?;
            match rhs {
                Value::Bool(b) => Value::Bool(*b),
                _ => miette::bail!("Expected bool, found {:?}", tokens[1]),
            }
        }
        Op::NotEqual => {
            let lhs = eval_ast(env, &tokens[0])?;
            let lhs = lhs.try_value()?;
            let rhs = eval_ast(env, &tokens[1])?;
            let rhs = rhs.try_value()?;
            lhs.not_equal(rhs)?
        }
        Op::EqualEqual => {
            assert!(tokens.len() == 2);
            let lhs = eval_ast(env, &tokens[0])?;
            let lhs = lhs.try_value()?;
            let rhs = eval_ast(env, &tokens[1])?;
            let rhs = rhs.try_value()?;
            lhs.equal(rhs)?
        }
        Op::Greater => {
            let lhs = eval_ast(env, &tokens[0])?;
            let lhs = lhs.try_value()?;
            let rhs = eval_ast(env, &tokens[1])?;
            let rhs = rhs.try_value()?;
            lhs.greater(rhs)?
        }
        Op::GreaterEqual => {
            let lhs = eval_ast(env, &tokens[0])?;
            let lhs = lhs.try_value()?;
            let rhs = eval_ast(env, &tokens[1])?;
            let rhs = rhs.try_value()?;
            lhs.greater_equal(rhs)?
        }
        Op::Less => {
            let lhs = eval_ast(env, &tokens[0])?;
            let lhs = lhs.try_value()?;
            let rhs = eval_ast(env, &tokens[1])?;
            let rhs = rhs.try_value()?;
            lhs.less(rhs)?
        }
        Op::LessEqual => {
            let lhs = eval_ast(env, &tokens[0])?;
            let lhs = lhs.try_value()?;
            let rhs = eval_ast(env, &tokens[1])?;
            let rhs = rhs.try_value()?;
            lhs.less_equal(rhs)?
        }
        Op::List => {
            if tokens.is_empty() {
                return Ok(Resolver::new(env, Object::Value(Value::List(List::new()))));
            }

            let mut list = Vec::with_capacity(tokens.len());
            let mut iter = tokens.iter();
            let first = eval_ast(env, iter.next().unwrap())?.to_value()?;
            let kind = first.kind();
            list.push(first);

            for token in iter {
                let value = eval_ast(env, token)?.to_value()?;
                if value.kind() != kind {
                    miette::bail!("List elements must have the same type");
                }
                list.push(value);
            }

            Value::List(list.into())
        }
        Op::Map => {
            if tokens.is_empty() {
                return Ok(Resolver::new(env, Object::Value(Value::Map(Map::new()))));
            }

            let mut iter = tokens.iter();
            let first_key = eval_ast(env, iter.next().expect("Key must be present"))?.to_value()?;
            let first_value =
                eval_ast(env, iter.next().expect("Value must be present"))?.to_value()?;
            let key_kind = KeyKind::try_from(first_key.kind())?;

            let mut map = HashMap::new();
            map.insert(Key::try_from(first_key)?, first_value);

            while let (Some(key), Some(value)) = (iter.next(), iter.next()) {
                let key = eval_ast(env, key)?.to_value()?;
                let value = eval_ast(env, value)?.to_value()?;
                let kk = KeyKind::try_from(key.kind())?;
                if kk != key_kind {
                    miette::bail!("Map elements must have the same type");
                }
                map.insert(Key::try_from(key)?, value);
            }

            Value::Map(map.into())
        }
        Op::IfTernary => {
            let lhs = match eval_ast(env, &tokens[0])?.try_value()? {
                Value::Bool(b) => *b,
                _ => miette::bail!("Expected bool, found {:?}", tokens[0]),
            };

            if lhs {
                return eval_ast(env, &tokens[1]);
            } else {
                return eval_ast(env, &tokens[2]);
            }
        }
        Op::Group => return eval_ast(env, &tokens[0]),
        Op::In => {
            let lhs = eval_ast(env, &tokens[0])?.to_value()?;
            match eval_ast(env, &tokens[1])?.try_value()? {
                Value::List(list) => Value::Bool(list.contains(&lhs)?),
                Value::Map(map) => Value::Bool(map.contains_key(&Key::try_from(lhs)?)?),
                _ => miette::bail!("Expected list, found {:?}", tokens[1]),
            }
        }
        Op::For => miette::bail!("For loop is not supported"),
        Op::While => miette::bail!("While loop is not supported"),
        Op::Var => miette::bail!("Var is not supported"),
    };
    Ok(Resolver::new(env, Object::Value(value)))
}

/// Resolver is a helper struct that helps to resolve the object to a value.
/// The object can be a value or an identifier.
/// If the object is an identifier, it should be resolved in the given environment.
///
/// The resolver should be used based on the context in which it is used.
pub struct Resolver<'a> {
    env: &'a Environment<'a>,
    object: Object<'a>,
}

impl Resolver<'_> {
    fn new<'a>(env: &'a Environment, object: Object<'a>) -> Resolver<'a> {
        Resolver { env, object }
    }

    /// Converts a resolver to a value. If the object is an identifier,
    /// it tries to resolve it in the given environment as a variable.
    ///
    /// Functions are resolved with try_function method.
    pub fn to_value(self) -> Result<Value, Error> {
        Ok(self.try_value()?.clone())
    }

    /// Tries to resolves to the value. If the object type is
    /// an identifier, it tries to resolve it in the given environment.
    /// Otherwise, returns a pointer to a constant value.
    pub fn try_value(&self) -> Result<&Value, Error> {
        match &self.object {
            Object::Value(val) => Ok(val),
            Object::Ident(ident) => {
                if let Some(val) = self.env.lookup_variable(*ident) {
                    Ok(val)
                } else {
                    miette::bail!("Variable not found: {}", ident);
                }
            }
        }
    }

    /// Tries to resolve to a function. If the object type is an identifier,
    /// it tries to resolve it in the given environment. Otherwise, returns
    /// an Error
    pub fn try_function(&self) -> Result<&Function, Error> {
        match &self.object {
            Object::Ident(ident) => {
                if let Some(f) = self.env.lookup_function(ident) {
                    Ok(f)
                } else {
                    miette::bail!("Function not found: {}", ident);
                }
            }
            _ => miette::bail!("Expected function name, found {:?}", self.object),
        }
    }
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
enum Object<'a> {
    Value(Value),
    Ident(&'a str),
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
            Value::List(vec!["hello".into(), Value::String("world".to_string())].into())
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
        env.set_variable("x", 42i64).expect("to set variable");

        let env = env.build();
        assert_eq!(eval(&env, "x.foo()").expect("x.foo()"), Value::Int(1));
    }

    #[test]
    fn test_index_map_access() {
        let mut env = EnvironmentBuilder::default();
        env.set_variable("x", {
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
        env.set_variable("x", {
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
