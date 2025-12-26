use cellang::Runtime;
use cellang::value::{IntoValue, ListValue, MapValue, Value};
use miette::Result;

fn main() -> Result<()> {
    let mut builder = Runtime::builder();
    builder.set_variable("assets", sample_assets())?;
    let runtime = builder.build();

    let has_high_risk =
        runtime.eval("assets.exists(asset, asset.risk >= 75)")?;
    assert_eq!(has_high_risk, Value::Bool(true));

    let prod_names = runtime.eval(
        "assets.filter(asset, 'prod' in asset.tags).map(asset, asset.name)",
    )?;
    assert_eq!(prod_names, vec!["scanner", "api"].into_value());

    let all_positive =
        runtime.eval("assets.map(asset, asset.risk).all(risk, risk >= 0)")?;
    assert_eq!(all_positive, Value::Bool(true));

    Ok(())
}

fn sample_assets() -> Value {
    let entries = vec![
        asset("scanner", 80, &["prod", "pci"]),
        asset("api", 65, &["prod"]),
        asset("etl", 40, &["batch"]),
    ];
    Value::List(ListValue::from(entries))
}

fn asset(name: &str, risk: i64, tags: &[&str]) -> Value {
    let mut record = MapValue::new();
    record.insert("name", name);
    record.insert("risk", risk);
    record.insert(
        "tags",
        ListValue::from(tags.iter().copied().collect::<Vec<_>>()),
    );
    Value::Map(record)
}
