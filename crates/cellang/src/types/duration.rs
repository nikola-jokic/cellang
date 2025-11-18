use core::fmt;
use miette::Error;
use serde::{Deserialize, Serialize, Serializer};
use std::{
    ops::{Deref, DerefMut},
    str::FromStr,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Duration(pub time::Duration);

impl Deref for Duration {
    type Target = time::Duration;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Duration {
    pub fn inner(&self) -> time::Duration {
        self.0
    }
}

impl From<time::Duration> for Duration {
    fn from(duration: time::Duration) -> Self {
        Duration(duration)
    }
}

impl From<Duration> for time::Duration {
    fn from(duration: Duration) -> Self {
        duration.0
    }
}

impl DerefMut for Duration {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

pub(crate) fn serialize_duration<S>(
    duration: &time::Duration,
    serializer: S,
) -> Result<S::Ok, S::Error>
where
    S: Serializer,
{
    Duration(*duration).serialize(serializer)
}

pub(crate) fn deserialize_duration<'de, D>(
    deserializer: D,
) -> Result<time::Duration, D::Error>
where
    D: serde::de::Deserializer<'de>,
{
    let s = String::deserialize(deserializer)?;
    let duration = Duration::from_str(&s).map_err(serde::de::Error::custom)?;
    Ok(duration.0)
}

impl FromStr for Duration {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut result = time::Duration::ZERO;
        let mut acc = 0i64;
        let mut chars = s.chars().peekable();
        while let Some(c) = chars.next() {
            match c {
                c if c.is_ascii_digit() => {
                    let d = c.to_digit(10).unwrap() as i64;
                    acc = acc * 10 + d;
                    continue;
                }
                'd' => {
                    result += time::Duration::days(acc);
                    acc = 0;
                }
                'h' => {
                    result += time::Duration::hours(acc);
                    acc = 0;
                }
                'm' => {
                    if chars.peek() == Some(&'s') {
                        result += time::Duration::milliseconds(acc);
                        chars.next();
                        acc = 0;
                    } else {
                        result += time::Duration::minutes(acc);
                        acc = 0;
                    }
                }
                's' => {
                    result += time::Duration::seconds(acc);
                    acc = 0;
                }
                'n' => {
                    if chars.peek() == Some(&'s') {
                        result += time::Duration::nanoseconds(acc);
                        chars.next();
                        acc = 0;
                    } else {
                        miette::bail!("Invalid type for duration: {s}",);
                    }
                }
                _ => miette::bail!("Invalid type for duration: {s}",),
            }
        }

        if acc != 0 {
            miette::bail!("Invalid type for duration: {:?}", s);
        }

        if result == time::Duration::ZERO {
            miette::bail!("Invalid type for duration: {:?}", s);
        }

        Ok(Duration(result))
    }
}

impl fmt::Display for Duration {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut duration = self.0;
        if duration.whole_days() > 0 {
            write!(f, "{}d", duration.whole_days())?;
            duration -= time::Duration::days(duration.whole_days());
        }
        if duration.whole_hours() > 0 {
            write!(f, "{}h", duration.whole_hours())?;
            duration -= time::Duration::hours(duration.whole_hours());
        }
        if duration.whole_minutes() > 0 {
            write!(f, "{}m", duration.whole_minutes())?;
            duration -= time::Duration::minutes(duration.whole_minutes());
        }
        if duration.whole_seconds() > 0 {
            write!(f, "{}s", duration.whole_seconds())?;
            duration -= time::Duration::seconds(duration.whole_seconds());
        }
        if duration.whole_milliseconds() > 0 {
            write!(f, "{}ms", duration.whole_milliseconds())?;
            duration -= time::Duration::milliseconds(
                duration.whole_milliseconds() as i64,
            );
        }
        if duration.whole_nanoseconds() > 0 {
            write!(f, "{}ns", duration.whole_nanoseconds())?;
        }
        Ok(())
    }
}

impl Serialize for Duration {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.to_string().serialize(serializer)
    }
}

impl<'de> serde::de::Deserialize<'de> for Duration {
    fn deserialize<D>(deserializer: D) -> Result<Duration, D::Error>
    where
        D: serde::de::Deserializer<'de>,
    {
        let s = String::deserialize(deserializer)?;
        Duration::from_str(&s).map_err(serde::de::Error::custom)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_duration_from_str() {
        assert_eq!(
            "1d".parse::<Duration>().unwrap().0,
            time::Duration::days(1)
        );
        assert_eq!(
            "1h".parse::<Duration>().unwrap().0,
            time::Duration::hours(1)
        );
        assert_eq!(
            "1m".parse::<Duration>().unwrap().0,
            time::Duration::minutes(1)
        );
        assert_eq!(
            "1s".parse::<Duration>().unwrap().0,
            time::Duration::seconds(1)
        );
        assert_eq!(
            "1ms".parse::<Duration>().unwrap().0,
            time::Duration::milliseconds(1)
        );
        assert_eq!(
            "1ns".parse::<Duration>().unwrap().0,
            time::Duration::nanoseconds(1)
        );
        assert_eq!(
            "1d1h1m1s1ms1ns".parse::<Duration>().unwrap().0,
            time::Duration::days(1)
                + time::Duration::hours(1)
                + time::Duration::minutes(1)
                + time::Duration::seconds(1)
                + time::Duration::milliseconds(1)
                + time::Duration::nanoseconds(1)
        );
    }

    #[test]
    fn test_duration_display() {
        assert_eq!(format!("{}", Duration(time::Duration::days(1))), "1d");
        assert_eq!(format!("{}", Duration(time::Duration::hours(1))), "1h");
        assert_eq!(format!("{}", Duration(time::Duration::minutes(1))), "1m");
        assert_eq!(format!("{}", Duration(time::Duration::seconds(1))), "1s");
        assert_eq!(
            format!("{}", Duration(time::Duration::milliseconds(1))),
            "1ms"
        );
        assert_eq!(
            format!("{}", Duration(time::Duration::nanoseconds(1))),
            "1ns"
        );
        assert_eq!(
            format!(
                "{}",
                Duration(
                    time::Duration::days(1)
                        + time::Duration::hours(1)
                        + time::Duration::minutes(1)
                        + time::Duration::seconds(1)
                        + time::Duration::milliseconds(1)
                        + time::Duration::nanoseconds(1)
                )
            ),
            "1d1h1m1s1ms1ns"
        );
    }
}
