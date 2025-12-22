use crate::error::RuntimeError;
use crate::runtime::RuntimeBuilder;
use crate::value::Value;
use regex::Regex;
use time::{Duration, OffsetDateTime, format_description::well_known::Rfc3339};

pub(crate) fn register(
    builder: &mut RuntimeBuilder,
) -> Result<(), RuntimeError> {
    builder.register_function("size", size)?;
    builder.register_function("contains", contains)?;
    builder.register_function("startsWith", starts_with)?;
    builder.register_function("endsWith", ends_with)?;
    builder.register_function("matches", matches)?;
    builder.register_function("type", cel_type)?;
    builder.register_function("string", to_string_value)?;
    builder.register_function("int", to_int)?;
    builder.register_function("uint", to_uint)?;
    builder.register_function("timestamp", to_timestamp)?;
    builder.register_function("duration", to_duration)?;
    Ok(())
}

fn size(value: Value) -> Result<i64, RuntimeError> {
    let len = match value {
        Value::String(text) => text.len(),
        Value::Bytes(bytes) => bytes.len(),
        Value::List(list) => list.len(),
        Value::Map(map) => map.len(),
        other => {
            return Err(RuntimeError::new(format!(
                "size() expects string, bytes, list, or map but received {}",
                other.kind()
            )));
        }
    };
    Ok(len as i64)
}

fn contains(haystack: Value, needle: Value) -> Result<bool, RuntimeError> {
    match (haystack, needle) {
        (Value::String(text), Value::String(query)) => {
            Ok(text.contains(&query))
        }
        (Value::Bytes(bytes), Value::Bytes(pattern)) => {
            if pattern.is_empty() {
                return Ok(true);
            }
            Ok(bytes
                .windows(pattern.len())
                .any(|window| window == pattern.as_slice()))
        }
        (left, right) => Err(RuntimeError::new(format!(
            "contains() expects both arguments to be strings or bytes but received {} and {}",
            left.kind(),
            right.kind()
        ))),
    }
}

fn starts_with(text: String, prefix: String) -> bool {
    text.starts_with(&prefix)
}

fn ends_with(text: String, suffix: String) -> bool {
    text.ends_with(&suffix)
}

fn matches(text: String, pattern: String) -> Result<bool, RuntimeError> {
    let regex = Regex::new(&pattern).map_err(|err| {
        RuntimeError::with_source("invalid regex passed to matches()", err)
    })?;
    Ok(regex.is_match(&text))
}

fn cel_type(value: Value) -> Result<String, RuntimeError> {
    let ty = match value {
        Value::Struct(strct) => strct.type_name.to_string(),
        other => other.kind().to_string(),
    };
    Ok(ty)
}

fn to_string_value(value: Value) -> Result<String, RuntimeError> {
    match value {
        Value::Bool(flag) => Ok(flag.to_string()),
        Value::Int(num) => Ok(num.to_string()),
        Value::Uint(num) => Ok(num.to_string()),
        Value::Double(num) => Ok(num.to_string()),
        Value::String(text) => Ok(text),
        Value::Bytes(bytes) => Ok(String::from_utf8_lossy(&bytes).to_string()),
        Value::Null => Ok("null".to_string()),
        Value::Timestamp(ts) => ts.format(&Rfc3339).map_err(|err| {
            RuntimeError::with_source("failed to format timestamp", err)
        }),
        Value::Duration(duration) => Ok(format_duration(duration)),
        other => Err(RuntimeError::new(format!(
            "string() cannot convert values of kind {}",
            other.kind()
        ))),
    }
}

fn to_int(value: Value) -> Result<i64, RuntimeError> {
    match value {
        Value::Int(i) => Ok(i),
        Value::Uint(u) => Ok(u as i64),
        Value::Double(d) => Ok(d as i64),
        Value::String(text) => text.parse::<i64>().map_err(|err| {
            RuntimeError::with_source("string could not be parsed as int", err)
        }),
        Value::Timestamp(ts) => Ok(ts.unix_timestamp()),
        other => Err(RuntimeError::new(format!(
            "int() cannot convert values of kind {}",
            other.kind()
        ))),
    }
}

fn to_uint(value: Value) -> Result<u64, RuntimeError> {
    match value {
        Value::Uint(u) => Ok(u),
        Value::Int(i) => u64::try_from(i).map_err(|err| {
            RuntimeError::with_source(
                "int value cannot be represented as uint",
                err,
            )
        }),
        Value::Double(d) => {
            if !d.is_finite() || d < 0.0 {
                return Err(RuntimeError::new(
                    "uint() cannot convert negative or infinite doubles",
                ));
            }
            Ok(d.round() as u64)
        }
        Value::String(text) => text.parse::<u64>().map_err(|err| {
            RuntimeError::with_source("string could not be parsed as uint", err)
        }),
        other => Err(RuntimeError::new(format!(
            "uint() cannot convert values of kind {}",
            other.kind()
        ))),
    }
}

fn to_timestamp(value: Value) -> Result<OffsetDateTime, RuntimeError> {
    match value {
        Value::Timestamp(ts) => Ok(ts),
        Value::String(text) => {
            OffsetDateTime::parse(&text, &Rfc3339).map_err(|err| {
                RuntimeError::with_source(
                    "timestamp() expects RFC3339 strings",
                    err,
                )
            })
        }
        Value::Int(seconds) => OffsetDateTime::from_unix_timestamp(seconds)
            .map_err(|err| {
                RuntimeError::with_source("invalid unix timestamp", err)
            }),
        Value::Uint(seconds) => {
            let secs = i64::try_from(seconds).map_err(|err| {
                RuntimeError::with_source("invalid unix timestamp", err)
            })?;
            OffsetDateTime::from_unix_timestamp(secs).map_err(|err| {
                RuntimeError::with_source("invalid unix timestamp", err)
            })
        }
        other => Err(RuntimeError::new(format!(
            "timestamp() cannot convert values of kind {}",
            other.kind()
        ))),
    }
}

fn to_duration(value: Value) -> Result<Duration, RuntimeError> {
    match value {
        Value::Duration(duration) => Ok(duration),
        Value::String(text) => parse_duration(&text),
        other => Err(RuntimeError::new(format!(
            "duration() cannot convert values of kind {}",
            other.kind()
        ))),
    }
}

fn parse_duration(input: &str) -> Result<Duration, RuntimeError> {
    if input.is_empty() {
        return Err(RuntimeError::new("duration() expects a non-empty string"));
    }
    let mut result = Duration::ZERO;
    let mut acc: i64 = 0;
    let mut chars = input.chars().peekable();
    while let Some(ch) = chars.next() {
        if ch.is_ascii_digit() {
            acc = acc
                .checked_mul(10)
                .and_then(|value| value.checked_add((ch as i64) - 48))
                .ok_or_else(|| {
                    RuntimeError::new("duration() literal overflowed")
                })?;
            continue;
        }
        if acc == 0 {
            return Err(RuntimeError::new("duration() missing numeric value"));
        }
        match ch {
            'd' => {
                result += Duration::days(acc);
                acc = 0;
            }
            'h' => {
                result += Duration::hours(acc);
                acc = 0;
            }
            'm' => {
                if chars.peek() == Some(&'s') {
                    chars.next();
                    result += Duration::milliseconds(acc);
                } else {
                    result += Duration::minutes(acc);
                }
                acc = 0;
            }
            's' => {
                result += Duration::seconds(acc);
                acc = 0;
            }
            'n' => {
                if chars.peek() == Some(&'s') {
                    chars.next();
                    result += Duration::nanoseconds(acc);
                    acc = 0;
                } else {
                    return Err(RuntimeError::new(
                        "duration() literal has invalid unit",
                    ));
                }
            }
            _ => {
                return Err(RuntimeError::new(format!(
                    "duration() literal has unsupported unit '{ch}'"
                )));
            }
        }
    }

    if acc != 0 {
        return Err(RuntimeError::new("duration() literal has dangling value"));
    }

    if result == Duration::ZERO {
        return Err(RuntimeError::new(
            "duration() literal cannot resolve to zero",
        ));
    }

    Ok(result)
}

fn format_duration(duration: Duration) -> String {
    let mut remaining = duration;
    let mut buffer = String::new();

    let mut write_component = |value: i128, suffix: &str| {
        if value > 0 {
            buffer.push_str(&format!("{value}{suffix}"));
        }
    };

    let days = remaining.whole_days();
    write_component(days.into(), "d");
    remaining -= Duration::days(days);

    let hours = remaining.whole_hours();
    write_component(hours.into(), "h");
    remaining -= Duration::hours(hours);

    let minutes = remaining.whole_minutes();
    write_component(minutes.into(), "m");
    remaining -= Duration::minutes(minutes);

    let seconds = remaining.whole_seconds();
    write_component(seconds.into(), "s");
    remaining -= Duration::seconds(seconds);

    let millis = remaining.whole_milliseconds();
    write_component(millis, "ms");
    remaining -= Duration::milliseconds(millis as i64);

    let nanos = remaining.whole_nanoseconds();
    write_component(nanos, "ns");

    if buffer.is_empty() {
        buffer.push_str("0s");
    }

    buffer
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::{ListValue, MapValue, StructValue};

    fn list(values: Vec<Value>) -> Value {
        Value::List(ListValue::from(values))
    }

    fn map(entries: &[(&str, Value)]) -> Value {
        let mut map = MapValue::new();
        for (key, value) in entries {
            map.insert(*key, value.clone());
        }
        Value::Map(map)
    }

    #[test]
    fn size_handles_supported_types() {
        assert_eq!(size(Value::String("abc".into())).unwrap(), 3);
        assert_eq!(size(Value::Bytes(vec![1, 2, 3])).unwrap(), 3);
        assert_eq!(
            size(list(vec![Value::Int(1), Value::Int(2), Value::Int(3)]))
                .unwrap(),
            3
        );
        assert_eq!(
            size(map(&[("a", Value::Int(1)), ("b", Value::Int(2))])).unwrap(),
            2
        );
        assert!(size(Value::Bool(true)).is_err());
    }

    #[test]
    fn contains_supports_strings_and_bytes() {
        assert!(
            contains(
                Value::String("hello world".into()),
                Value::String("world".into())
            )
            .unwrap()
        );
        assert!(
            !contains(
                Value::String("hello".into()),
                Value::String("bye".into())
            )
            .unwrap()
        );
        assert!(
            contains(
                Value::Bytes(b"foobar".to_vec()),
                Value::Bytes(b"oba".to_vec())
            )
            .unwrap()
        );
        assert!(
            contains(Value::Bytes(b"test".to_vec()), Value::Bytes(Vec::new()))
                .unwrap()
        );
        assert!(
            contains(Value::String("foo".into()), Value::Bytes(vec![1]))
                .is_err()
        );
    }

    #[test]
    fn starts_and_ends_with_work_for_strings() {
        assert!(starts_with("foobar".into(), "foo".into()));
        assert!(!starts_with("foobar".into(), "bar".into()));
        assert!(ends_with("foobar".into(), "bar".into()));
        assert!(!ends_with("foobar".into(), "foo".into()));
    }

    #[test]
    fn matches_validates_regex_and_reports_errors() {
        assert!(matches("abc123".into(), r"^abc\d+$".into()).unwrap());
        assert!(!matches("abc".into(), r"\d+".into()).unwrap());
        assert!(matches("abc".into(), "[".into()).is_err());
    }

    #[test]
    fn cel_type_returns_value_kind_or_struct() {
        assert_eq!(cel_type(Value::Int(1)).unwrap(), "int");
        let mut user = StructValue::new("acme.User");
        user.set_field("name", "A");
        assert_eq!(cel_type(Value::Struct(user)).unwrap(), "acme.User");
    }

    #[test]
    fn to_string_value_covers_core_types() {
        assert_eq!(to_string_value(Value::Bool(true)).unwrap(), "true");
        assert_eq!(to_string_value(Value::Int(42)).unwrap(), "42");
        assert_eq!(
            to_string_value(Value::Bytes(b"hi".to_vec())).unwrap(),
            "hi"
        );
        let ts = OffsetDateTime::from_unix_timestamp(1).unwrap();
        assert_eq!(
            to_string_value(Value::Timestamp(ts)).unwrap(),
            "1970-01-01T00:00:01Z"
        );
        let mut duration = Duration::hours(1);
        duration += Duration::minutes(2);
        duration += Duration::seconds(3);
        assert_eq!(
            to_string_value(Value::Duration(duration)).unwrap(),
            "1h2m3s"
        );
        assert!(to_string_value(Value::List(ListValue::new())).is_err());
    }

    #[test]
    fn to_int_and_uint_handle_conversions() {
        assert_eq!(to_int(Value::String("-42".into())).unwrap(), -42);
        let ts = OffsetDateTime::from_unix_timestamp(10).unwrap();
        assert_eq!(to_int(Value::Timestamp(ts)).unwrap(), 10);
        assert_eq!(to_uint(Value::Int(5)).unwrap(), 5);
        assert!(to_uint(Value::Int(-1)).is_err());
        assert!(to_uint(Value::Double(-1.0)).is_err());
    }

    #[test]
    fn to_timestamp_and_duration_parse_inputs() {
        let ts =
            to_timestamp(Value::String("1970-01-01T00:00:05Z".into())).unwrap();
        assert_eq!(ts.unix_timestamp(), 5);
        let from_int = to_timestamp(Value::Int(7)).unwrap();
        assert_eq!(from_int.unix_timestamp(), 7);
        assert!(to_timestamp(Value::Bool(true)).is_err());

        let duration =
            to_duration(Value::String("1h30m15s10ms".into())).unwrap();
        assert_eq!(
            duration,
            Duration::hours(1)
                + Duration::minutes(30)
                + Duration::seconds(15)
                + Duration::milliseconds(10)
        );
        assert!(to_duration(Value::Bool(false)).is_err());
    }

    #[test]
    fn parse_duration_and_format_duration_cover_edge_cases() {
        let parsed = parse_duration("2d3h4m5s6ms7ns").unwrap();
        assert_eq!(format_duration(parsed), "2d3h4m5s6ms7ns");
        assert!(parse_duration("").is_err());
        assert!(parse_duration("ms").is_err());
        assert!(parse_duration("1x").is_err());
    }
}
