use crate::error::RuntimeError;
use crate::runtime::RuntimeBuilder;
use crate::value::Value;
use regex::Regex;
use time::{format_description::well_known::Rfc3339, Duration, OffsetDateTime};

pub(crate) fn register(builder: &mut RuntimeBuilder) -> Result<(), RuntimeError> {
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
            )))
        }
    };
    Ok(len as i64)
}

fn contains(haystack: Value, needle: Value) -> Result<bool, RuntimeError> {
    match (haystack, needle) {
        (Value::String(text), Value::String(query)) => Ok(text.contains(&query)),
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
            left.kind(), right.kind()
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
    let regex = Regex::new(&pattern)
        .map_err(|err| RuntimeError::with_source("invalid regex passed to matches()", err))?;
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
        Value::Timestamp(ts) => ts
            .format(&Rfc3339)
            .map_err(|err| RuntimeError::with_source("failed to format timestamp", err)),
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
        Value::String(text) => text
            .parse::<i64>()
            .map_err(|err| RuntimeError::with_source("string could not be parsed as int", err)),
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
            RuntimeError::with_source("int value cannot be represented as uint", err)
        }),
        Value::Double(d) => {
            if !d.is_finite() || d < 0.0 {
                return Err(RuntimeError::new(
                    "uint() cannot convert negative or infinite doubles",
                ));
            }
            Ok(d.round() as u64)
        }
        Value::String(text) => text
            .parse::<u64>()
            .map_err(|err| RuntimeError::with_source("string could not be parsed as uint", err)),
        other => Err(RuntimeError::new(format!(
            "uint() cannot convert values of kind {}",
            other.kind()
        ))),
    }
}

fn to_timestamp(value: Value) -> Result<OffsetDateTime, RuntimeError> {
    match value {
        Value::Timestamp(ts) => Ok(ts),
        Value::String(text) => OffsetDateTime::parse(&text, &Rfc3339)
            .map_err(|err| RuntimeError::with_source("timestamp() expects RFC3339 strings", err)),
        Value::Int(seconds) => OffsetDateTime::from_unix_timestamp(seconds)
            .map_err(|err| RuntimeError::with_source("invalid unix timestamp", err)),
        Value::Uint(seconds) => {
            let secs = i64::try_from(seconds).map_err(|err| {
                RuntimeError::with_source("invalid unix timestamp", err)
            })?;
            OffsetDateTime::from_unix_timestamp(secs)
                .map_err(|err| RuntimeError::with_source("invalid unix timestamp", err))
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
                .ok_or_else(|| RuntimeError::new("duration() literal overflowed"))?;
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
                    return Err(RuntimeError::new("duration() literal has invalid unit"));
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
        return Err(RuntimeError::new("duration() literal cannot resolve to zero"));
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