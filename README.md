# duration-breakdown
Breakdowns of durations of time into their constituent parts of various units.

## Example

```rust
use duration_breakdown::DurationBreakdown;
use std::time::Duration;

let breakdown = DurationBreakdown::from(Duration::new(12_345_678, 1234));
assert_eq!(
    breakdown.to_string(),
    "20 weeks, 2 days, 21 hours, 21 minutes, 18 seconds, and 1234 nanoseconds");
```
