use cellang::{Runtime, Value};
use miette::Result;

fn main() -> Result<()> {
    let runtime = Runtime::builder().build();

    let value = cellang::eval(&runtime, "1 + 2 * 3")?;
    assert_eq!(value, Value::Int(7));

    let mut child = runtime.child_builder();
        child.set_variable("x", 2_i64)?;
    let runtime = child.build();
    let value = cellang::eval(&runtime, "x >= 2")?;
    assert_eq!(value, Value::Bool(true));

    let contains = runtime.eval("'World' in 'Hello, World!'")?;
    assert_eq!(contains, Value::Bool(true));

    Ok(())
}
