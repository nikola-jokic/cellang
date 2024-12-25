#[macro_export]
macro_rules! impl_value_conversions {
    ($($target_type: ty => $value_variant:path as $as_type: ty),* $(,)?) => {
        $(
            impl From<$target_type> for Value {
                fn from(value: $target_type) -> Self {
                    $value_variant(value as $as_type)
                }
            }
        )*
    }
}
