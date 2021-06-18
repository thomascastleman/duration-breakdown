//! This crate breaks down durations of time into their constituent parts of
//! various units (weeks, days, hours, minutes, seconds, and nanoseconds).
//!
//! This can be used to convert a duration such as 10,000 seconds into the
//! following form: 0 weeks, 0 days, 2 hours, 46 minutes, 40 seconds, and 0 nanoseconds.
//!
//! # Examples
//! ```
//! use duration_breakdown::DurationBreakdown;
//! use std::time::Duration;
//! let breakdown = DurationBreakdown::new(Duration::new(12_345_678, 1234));
//! assert_eq!(
//!     breakdown.to_string(),
//!     "20 weeks, 2 days, 21 hours, 21 minutes, 18 seconds, and 1234 nanoseconds");
//! ```
use std::{fmt, time};

const MINUTE_IN_SECS: u64 = 60;
const HOUR_IN_SECS: u64 = MINUTE_IN_SECS * 60;
const DAY_IN_SECS: u64 = HOUR_IN_SECS * 24;
const WEEK_IN_SECS: u64 = DAY_IN_SECS * 7;

/// A `DurationBreakdown` represents a duration of time that has been
/// broken up into several units (i.e. weeks, days, etc) in such a way
/// that the sum of each unit comprises the whole duration of time.
#[derive(PartialEq, Debug)]
pub struct DurationBreakdown {
    weeks: u64,
    days: u64,
    hours: u64,
    minutes: u64,
    seconds: u64,
    nanoseconds: u64,
}

impl DurationBreakdown {
    /// Constructs a new duration breakdown, given an instance of `std::time::Duration`.
    pub fn new(duration: time::Duration) -> Self {
        let mut seconds_left = duration.as_secs();

        let weeks = seconds_left / WEEK_IN_SECS;
        seconds_left %= WEEK_IN_SECS;

        let days = seconds_left / DAY_IN_SECS;
        seconds_left %= DAY_IN_SECS;

        let hours = seconds_left / HOUR_IN_SECS;
        seconds_left %= HOUR_IN_SECS;

        let minutes = seconds_left / MINUTE_IN_SECS;
        seconds_left %= MINUTE_IN_SECS;

        let seconds = seconds_left;
        let nanoseconds = duration.subsec_nanos() as u64;

        DurationBreakdown {
            weeks,
            days,
            hours,
            minutes,
            seconds,
            nanoseconds,
        }
    }

    /// Constructs a `DurationBreakdown` directly from the given component parts.
    pub fn from_parts(
        weeks: u64,
        days: u64,
        hours: u64,
        minutes: u64,
        seconds: u64,
        nanoseconds: u64,
    ) -> Self {
        DurationBreakdown {
            weeks,
            days,
            hours,
            minutes,
            seconds,
            nanoseconds,
        }
    }

    /// Gets the number of weeks in the breakdown.
    pub fn weeks(&self) -> u64 {
        self.weeks
    }

    /// Gets the number of days in the breakdown.
    pub fn days(&self) -> u64 {
        self.days
    }

    /// Gets the number of hours in the breakdown.
    pub fn hours(&self) -> u64 {
        self.hours
    }

    /// Gets the number of minutes in the breakdown.
    pub fn minutes(&self) -> u64 {
        self.minutes
    }

    /// Gets the number of seconds in the breakdown.
    pub fn seconds(&self) -> u64 {
        self.seconds
    }

    /// Gets the number of nanoseconds in the breakdown.
    pub fn nanoseconds(&self) -> u64 {
        self.nanoseconds
    }

    // Determines whether or not to attach a plural suffix.
    fn plural(quantity: u64) -> String {
        (if quantity == 1 { "" } else { "s" }).to_string()
    }

    /// A string describing the number of weeks in the breakdown. E.g. `"14 weeks"`.
    pub fn weeks_as_string(&self) -> String {
        format!(
            "{} week{}",
            self.weeks,
            DurationBreakdown::plural(self.weeks)
        )
    }

    /// A string describing the number of days in the breakdown. E.g. `"6 days"`.
    pub fn days_as_string(&self) -> String {
        format!("{} day{}", self.days, DurationBreakdown::plural(self.days))
    }

    /// A string describing the number of hours in the breakdown. E.g. `"1 hour"`.
    pub fn hours_as_string(&self) -> String {
        format!(
            "{} hour{}",
            self.hours,
            DurationBreakdown::plural(self.hours)
        )
    }

    /// A string describing the number of minutes in the breakdown. E.g. `"53 minutes"`.
    pub fn minutes_as_string(&self) -> String {
        format!(
            "{} minute{}",
            self.minutes,
            DurationBreakdown::plural(self.minutes)
        )
    }

    /// A string describing the number of seconds in the breakdown. E.g. `"40 seconds"`.
    pub fn seconds_as_string(&self) -> String {
        format!(
            "{} second{}",
            self.seconds,
            DurationBreakdown::plural(self.seconds)
        )
    }

    /// A string describing the number of nanoseconds in the breakdown. E.g. `"1700 nanoseconds"`.
    pub fn nanoseconds_as_string(&self) -> String {
        format!(
            "{} nanosecond{}",
            self.nanoseconds,
            DurationBreakdown::plural(self.nanoseconds)
        )
    }

    /// A string describing the entire `DurationBreakdown`. All components
    /// are included, even if their value is 0. See `as_string_hide_zeros`
    /// for an alternate display of the breakdown.
    ///
    /// Note that this function is used by the implementation of `Display` for
    /// `DurationBreakdown`.
    pub fn as_string(&self) -> String {
        format!(
            "{}, {}, {}, {}, {}, and {}",
            self.weeks_as_string(),
            self.days_as_string(),
            self.hours_as_string(),
            self.minutes_as_string(),
            self.seconds_as_string(),
            self.nanoseconds_as_string(),
        )
    }

    /// A string describing the entire `DurationBreakdown`, but any components
    /// that have a value of 0 are omitted from the description.
    pub fn as_string_hide_zeros(&self) -> String {
        let mut components: Vec<String> = vec![
            (self.weeks, self.weeks_as_string()),
            (self.days, self.days_as_string()),
            (self.hours, self.hours_as_string()),
            (self.minutes, self.minutes_as_string()),
            (self.seconds, self.seconds_as_string()),
            (self.nanoseconds, self.nanoseconds_as_string()),
        ]
        .into_iter()
        .filter_map(|(v, s)| if v != 0 { Some(s) } else { None })
        .collect();

        if let Some(last) = components.last_mut() {
            *last = format!("and {}", last);
        }

        components.join(", ")
    }
}

impl fmt::Display for DurationBreakdown {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_string())
    }
}

#[cfg(test)]
mod test {
    use std::time::Duration;

    use super::*;

    #[test]
    fn zero_duration_is_all_zeros() {
        assert_eq!(
            DurationBreakdown::new(Duration::new(0, 0)),
            DurationBreakdown {
                weeks: 0,
                days: 0,
                hours: 0,
                minutes: 0,
                seconds: 0,
                nanoseconds: 0,
            }
        );
    }

    #[test]
    fn two_hours() {
        assert_eq!(
            DurationBreakdown::new(Duration::from_secs(60 * 60 * 2)),
            DurationBreakdown {
                weeks: 0,
                days: 0,
                hours: 2,
                minutes: 0,
                seconds: 0,
                nanoseconds: 0,
            }
        )
    }

    #[test]
    fn more_complicated() {
        assert_eq!(
            DurationBreakdown::new(Duration::from_secs(15403)),
            DurationBreakdown {
                weeks: 0,
                days: 0,
                hours: 4,
                minutes: 16,
                seconds: 43,
                nanoseconds: 0,
            }
        )
    }

    #[test]
    fn with_nanoseconds() {
        assert_eq!(
            DurationBreakdown::new(Duration::from_nanos(4150)),
            DurationBreakdown {
                weeks: 0,
                days: 0,
                hours: 0,
                minutes: 0,
                seconds: 0,
                nanoseconds: 4150,
            }
        );
    }

    #[test]
    fn extracting_components() {
        let d = DurationBreakdown {
            weeks: 14,
            days: 5,
            hours: 20,
            minutes: 13,
            seconds: 48,
            nanoseconds: 1600,
        };

        assert_eq!(d.weeks(), 14);
        assert_eq!(d.days(), 5);
        assert_eq!(d.hours(), 20);
        assert_eq!(d.minutes(), 13);
        assert_eq!(d.seconds(), 48);
        assert_eq!(d.nanoseconds(), 1600);
    }

    #[test]
    fn from_parts() {
        let d = DurationBreakdown::from_parts(45, 10, 16, 0, 17, 450);
        assert_eq!(d.weeks(), 45);
        assert_eq!(d.days(), 10);
        assert_eq!(d.hours(), 16);
        assert_eq!(d.minutes(), 0);
        assert_eq!(d.seconds(), 17);
        assert_eq!(d.nanoseconds(), 450);
    }

    #[test]
    fn hide_zeros() {
        let d = DurationBreakdown::from_parts(40, 0, 0, 16, 1, 0);
        assert_eq!(
            d.as_string_hide_zeros(),
            "40 weeks, 16 minutes, and 1 second"
        );
        let d = DurationBreakdown::new(Duration::new(0, 0));
        assert_eq!(d.as_string_hide_zeros(), "");
    }
}
