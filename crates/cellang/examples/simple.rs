use cellang::{Runtime, Value};
use miette::Result;

fn main() -> Result<()> {
    let runtime = Runtime::builder().build();

    let value = cellang::eval(&runtime, "1 + 2 * 3")?;
    assert_eq!(value, Value::Int(7));

    let grouped = runtime.eval("(1 + 2) * 3")?;
    assert_eq!(grouped, Value::Int(9));

    let ternary = runtime.eval("1 < 2 ? 'yes' : 'no'")?;
    assert_eq!(ternary, Value::String("yes".to_string()));

    let list_lookup = runtime.eval("[10, 20, 30][1]")?;
    assert_eq!(list_lookup, Value::Int(20));

    let map_lookup = runtime.eval("{'region': 'eu', 'retries': 3}.region")?;
    assert_eq!(map_lookup, Value::String("eu".to_string()));

    let mut child = runtime.child_builder();
    child.set_variable("x", 2_i64)?;
    let runtime = child.build();
    let value = cellang::eval(&runtime, "x >= 2")?;
    assert_eq!(value, Value::Bool(true));

    let decision = runtime.eval("x in [1, 2, 3] && x != 4")?;
    assert_eq!(decision, Value::Bool(true));

    let contains = runtime.eval("'World' in 'Hello, World!'")?;
    assert_eq!(contains, Value::Bool(true));

    Ok(())
}
