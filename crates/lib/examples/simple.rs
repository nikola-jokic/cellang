use cellang::EnvironmentBuilder;

fn main() {
    // Create a new environment with functions but without variables
    let env = EnvironmentBuilder::default();
    let env = env.build();

    // Evaluate a simple expression
    let value = cellang::eval(&env, "1 + 2 * 3").unwrap();
    assert_eq!(value, 7i64.into());

    // Evaluate a simple expression with variables
    let mut env = env.child_builder();
    env.set_variable("x", 2i64).unwrap();
    let env = env.build();
    let value = cellang::eval(&env, "x >= 2").unwrap();
    assert_eq!(value, true.into());

    // Evaluate a simple expression with macros
    let env = EnvironmentBuilder::default();
    let env = env.build();
    let value = cellang::eval(&env, "'Hello, World!'.startsWith('Hello')").unwrap();
    assert_eq!(value, true.into());
}
