use cellang::{eval, eval_ast, Environment, List, Map, TokenTree, Value};
use miette::Error;

/// Let's create a function to split a string on a given character.
/// By the very nature of CEL, this function can be called like the following:
/// ```
/// 'a,b,c'.split(',')
/// // OR
/// split('a,b,c', ',')
/// // Or by using variables
/// x.split(',')
/// ```
fn split(env: &Environment, tokens: &[TokenTree]) -> Result<Value, Error> {
    // We expect two arguments: the string to split and the character to split on
    //
    // The parser would transform x.split(',') into split(x, ',')
    if tokens.len() != 2 {
        miette::bail!("Expected two arguments");
    }

    // Evaluate the first argument
    // The value of the argument should be of type Value::String
    // However, it may also be a reference to a variable that is of type string
    let string = match eval_ast(env, &tokens[0])?.to_value(env)? {
        Value::String(string) => string,
        _ => miette::bail!("Expected a string as the first argument"),
    };

    // Evaluate the second argument
    // The value of the argument should be of type Value::String since there
    // are no character types in CEL
    let character = match eval_ast(env, &tokens[1])?.to_value(env)? {
        Value::String(character) if character.len() == 1 => character.chars().next().unwrap(),
        _ => miette::bail!("Expected a string as the second argument"),
    };

    // Now, we are in the rust land. We can use the standard library to split the string
    // on the character and return the result
    let result = string
        .split(character)
        .map(|s| s.into())
        .collect::<Vec<Value>>();

    // Now, return the type List of strings
    Ok(Value::List(result.into()))
}

fn main() {
    // Create a new environment with functions but without variables
    let mut env = Environment::new();

    // Register the function
    env.set_function("split", Box::new(split));

    // Evaluate a simple expression
    let value = eval(&env, "'a,b,c'.split(',')").unwrap();
    assert_eq!(
        value,
        Value::List(List::from(vec![
            "a".to_string(),
            "b".to_string(),
            "c".to_string()
        ]))
    );

    // Evaluate a simple expression with variables
    let mut variables = Map::new();
    variables.insert("x".into(), "a,b,c".into()).unwrap();
    let env = env.child().with_variables(variables);
    let value = eval(&env, "x.split(',')").unwrap();
    assert_eq!(
        value,
        Value::List(List::from(vec![
            "a".to_string(),
            "b".to_string(),
            "c".to_string()
        ]))
    );
}
