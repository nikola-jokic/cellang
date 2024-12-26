use cellang::{eval, Environment, Map};

fn main() {
    // Create a new environment with functions but without variables
    let env = Environment::new();

    // Evaluate a simple expression
    let value = eval(&env, "1 + 2 * 3").unwrap();
    assert_eq!(value, 7i64.into());

    // Evaluate a simple expression with variables
    let mut variables = Map::new();
    variables.insert("x".into(), 2i64.into()).unwrap();
    let env = env.child().with_variables(variables);
    let value = eval(&env, "x >= 2").unwrap();
    assert_eq!(value, true.into());

    // Evaluate a simple expression with macros
    let env = Environment::new();
    let value = eval(&env, "'Hello, World!'.startsWith('Hello')").unwrap();
    assert_eq!(value, true.into());
}
