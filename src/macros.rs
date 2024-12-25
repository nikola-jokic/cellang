#[macro_export]
macro_rules! impl_value_conversions {
    ($($target_type: ty => $value_variant:path),* $(,)?) => {
        $(
            impl From<$target_type> for Value {
                fn from(value: $target_type) -> Self {
                    $value_variant(value)
                }
            }

            impl From<Value> for $target_type {
                fn from(value: Value) -> Self {
                    match value {
                        $value_variant(v) => v,
                        _ => panic!("Invalid conversion from {:?} to {:?}", value, stringify!($target_type)),
                    }
                }
            }
        )*
    }
}
