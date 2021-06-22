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
//! let breakdown = DurationBreakdown::from(Duration::new(12_345_678, 1234));
//! assert_eq!(
//!     breakdown.to_string(),
//!     "20 weeks, 2 days, 21 hours, 21 minutes, 18 seconds, and 1234 nanoseconds");
//! ```

use std::{
    convert::{From, TryFrom},
    fmt::{self, Display},
    time::Duration,
};

// Constants for converting between units of time.
const NS_PER_SEC: u64 = 1_000_000_000;
const SEC_PER_MIN: u64 = 60;
const MIN_PER_HOUR: u64 = 60;
const HOUR_PER_DAY: u64 = 24;
const DAY_PER_WEEK: u64 = 7;

// We access a `std::time::Duration`'s total duration in seconds,
// so these facilitate conversion into a breakdown.
const SEC_PER_HOUR: u64 = SEC_PER_MIN * 60;
const SEC_PER_DAY: u64 = SEC_PER_HOUR * 24;
const SEC_PER_WEEK: u64 = SEC_PER_DAY * 7;

/// A `DurationBreakdown` represents a duration of time that has been
/// broken up into several units (i.e. weeks, days, etc) in such a way
/// that the sum of each unit comprises the whole duration of time.
#[derive(Eq, PartialEq, Debug, Clone, Copy)]
pub struct DurationBreakdown {
    weeks: u64,
    days: u64,
    hours: u64,
    minutes: u64,
    seconds: u64,
    nanoseconds: u64,
}

impl DurationBreakdown {
    /// Constructs a `DurationBreakdown` directly from the given component parts.
    ///
    /// # Examples
    /// ```
    /// # use duration_breakdown::DurationBreakdown;
    /// let breakdown = DurationBreakdown::from_parts(
    ///     4,   // weeks
    ///     2,   // days
    ///     17,  // hours
    ///     41,  // minutes
    ///     18,  // seconds
    ///     100, // nanoseconds
    /// );
    /// assert_eq!(breakdown.weeks(), 4);
    /// assert_eq!(breakdown.days(), 2);
    /// assert_eq!(breakdown.hours(), 17);
    /// assert_eq!(breakdown.minutes(), 41);
    /// assert_eq!(breakdown.seconds(), 18);
    /// assert_eq!(breakdown.nanoseconds(), 100);
    /// ```
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

    /// Converts a `DurationBreakdown` into a standard form in which the value
    /// of a given time component (week, day, etc) is no greater than the value
    /// of a single unit of the time component one level up. For instance,
    /// a `DurationBreakdown` with 68 as its minutes value and 3 as its
    /// hours value would be normalized to 8 minutes and 4 hours.
    ///
    /// # Examples
    /// ```
    /// # use duration_breakdown::DurationBreakdown;
    /// // 9 days, 1 hour, 50 minutes, 70 seconds (not normalized)
    /// let mut breakdown = DurationBreakdown::from_parts(0, 9, 1, 50, 70, 0);
    /// breakdown.normalize();
    /// assert_eq!(
    ///     breakdown.as_string(),
    ///     "1 week, 2 days, 1 hour, 51 minutes, 10 seconds, and 0 nanoseconds");
    /// ```
    pub fn normalize(&mut self) {
        // propagate "overflow" upwards from the smallest unit (ns)
        if self.nanoseconds >= NS_PER_SEC {
            self.seconds += self.nanoseconds / NS_PER_SEC;
            self.nanoseconds %= NS_PER_SEC;
        }
        if self.seconds >= SEC_PER_MIN {
            self.minutes += self.seconds / SEC_PER_MIN;
            self.seconds %= SEC_PER_MIN;
        }
        if self.minutes >= MIN_PER_HOUR {
            self.hours += self.minutes / MIN_PER_HOUR;
            self.minutes %= MIN_PER_HOUR;
        }
        if self.hours >= HOUR_PER_DAY {
            self.days += self.hours / HOUR_PER_DAY;
            self.hours %= HOUR_PER_DAY;
        }
        if self.days >= DAY_PER_WEEK {
            self.weeks += self.days / DAY_PER_WEEK;
            self.days %= DAY_PER_WEEK;
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
    ///
    /// # Examples
    /// ```
    /// # use duration_breakdown::DurationBreakdown;
    /// let breakdown = DurationBreakdown::from_parts(0, 4, 0, 10, 48, 200);
    /// assert_eq!(
    ///     breakdown.as_string(),
    ///     "0 weeks, 4 days, 0 hours, 10 minutes, 48 seconds, and 200 nanoseconds");
    /// ```
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
    /// that have a value of 0 are omitted from the description. See
    /// `as_string` for a version of this function that includes 0-valued
    /// components.
    ///
    /// # Examples
    /// ```
    /// # use duration_breakdown::DurationBreakdown;
    /// let breakdown = DurationBreakdown::from_parts(0, 4, 0, 10, 48, 200);
    /// assert_eq!(
    ///     breakdown.as_string_hide_zeros(),
    ///     "4 days, 10 minutes, 48 seconds, and 200 nanoseconds");
    /// ```
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

impl Display for DurationBreakdown {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_string())
    }
}

impl From<Duration> for DurationBreakdown {
    /// Constructs a new duration breakdown, given an instance of `std::time::Duration`.
    fn from(duration: Duration) -> Self {
        let mut seconds_left = duration.as_secs();

        let weeks = seconds_left / SEC_PER_WEEK;
        seconds_left %= SEC_PER_WEEK;

        let days = seconds_left / SEC_PER_DAY;
        seconds_left %= SEC_PER_DAY;

        let hours = seconds_left / SEC_PER_HOUR;
        seconds_left %= SEC_PER_HOUR;

        let minutes = seconds_left / SEC_PER_MIN;
        seconds_left %= SEC_PER_MIN;

        let seconds = seconds_left;
        let nanoseconds = u64::from(duration.subsec_nanos());

        DurationBreakdown {
            weeks,
            days,
            hours,
            minutes,
            seconds,
            nanoseconds,
        }
    }
}

impl From<DurationBreakdown> for Duration {
    /// Constructs a new `std::time::Duration`, given a `DurationBreakdown`.
    ///
    /// # Panics
    /// This will panic if the `DurationBreakdown`'s nanoseconds value is
    /// greater than `u32::MAX`.
    fn from(db: DurationBreakdown) -> Self {
        Duration::new(
            (db.weeks * SEC_PER_WEEK)
                + (db.days * SEC_PER_DAY)
                + (db.hours * SEC_PER_HOUR)
                + (db.minutes * SEC_PER_MIN)
                + (db.seconds),
            u32::try_from(db.nanoseconds)
                .expect("DurationBreakdown's nanoseconds value greater than max u32"),
        )
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use quickcheck::quickcheck;
    use std::time::Duration;

    #[test]
    fn zero_duration_is_all_zeros() {
        assert_eq!(
            DurationBreakdown::from(Duration::new(0, 0)),
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
            DurationBreakdown::from(Duration::from_secs(60 * 60 * 2)),
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
            DurationBreakdown::from(Duration::from_secs(15403)),
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
            DurationBreakdown::from(Duration::from_nanos(4150)),
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
        let d = DurationBreakdown::from(Duration::new(0, 0));
        assert_eq!(d.as_string_hide_zeros(), "");
    }

    #[test]
    fn duration_from_breakdown() {
        let db = DurationBreakdown::from_parts(0, 0, 2, 13, 48, 700);
        assert_eq!(Duration::from(db), Duration::new(8028, 700));
    }

    #[test]
    fn normalize() {
        let mut breakdown = DurationBreakdown::from_parts(0, 9, 1, 50, 70, 0);
        breakdown.normalize();
        assert_eq!(breakdown.weeks(), 1);
        assert_eq!(breakdown.days(), 2);
        assert_eq!(breakdown.hours(), 1);
        assert_eq!(breakdown.minutes(), 51);
        assert_eq!(breakdown.seconds(), 10);
        assert_eq!(breakdown.nanoseconds(), 0);
    }

    #[test]
    fn max_breakdown() {
        // Duration::MAX is platform dependent, so this test
        // just makes sure that creating a breakdown doesn't panic
        DurationBreakdown::from(Duration::MAX);
    }

    fn breakdown_from_secs(secs: u64) -> DurationBreakdown {
        DurationBreakdown::from(Duration::from_secs(secs))
    }

    quickcheck! {
        // Weeks is total seconds divided by how many seconds
        // are in a week
        fn weeks_is_sec_over_sec_per_week(secs: u64) -> bool {
            let b = breakdown_from_secs(secs);
            b.weeks() == secs / SEC_PER_WEEK
        }

        // Days is whatever is left over after taking out weeks,
        // divided by number of seconds in a day
        fn days_is_leftover_sec_per_day(secs: u64) -> bool {
            let b = breakdown_from_secs(secs);
            b.days() == (secs % SEC_PER_WEEK) / SEC_PER_DAY
        }

        // Hours is whatever is left over after taking out days,
        // divided by number of seconds in an hour
        fn hours_is_leftover_sec_per_hour(secs: u64) -> bool {
            let b = breakdown_from_secs(secs);
            b.hours() == (secs % SEC_PER_DAY) / SEC_PER_HOUR
        }

        // Minutes is whatever is left over after taking out hours,
        // divided by number of seconds in a minute
        fn minutes_is_leftover_sec_per_min(secs: u64) -> bool {
            let b = breakdown_from_secs(secs);
            b.minutes() == (secs % SEC_PER_HOUR) / SEC_PER_MIN
        }

        // Seconds is whatever is left over after taking out minutes.
        fn seconds_is_leftover_sec(secs: u64) -> bool {
            let b = breakdown_from_secs(secs);
            b.seconds() == (secs % SEC_PER_MIN)
        }

        // Converting from a duration to a breakdown and back should
        // yield the same duration.
        fn conversions_work(secs: u64) -> bool {
            let d = Duration::from_secs(secs);
            Duration::from(DurationBreakdown::from(d)) == d
        }
    }
}
