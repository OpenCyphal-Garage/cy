use duration_str::parse_time;
use num_traits::{PrimInt, Unsigned};
use std::ops::RangeInclusive;
use std::time::{SystemTime, UNIX_EPOCH};
use time::Duration;

pub fn is_prime<T>(value: T) -> bool
where
    T: PrimInt + Unsigned,
{
    let zero = T::zero();
    let one = T::one();
    let two = one + one;
    let three = two + one;
    if (value <= two) || (value % two == zero) {
        return value == two;
    }
    let mut divisor: T = three;
    while divisor <= value / divisor {
        if value % divisor == zero {
            return false;
        }
        divisor = divisor + two;
    }
    true
}

pub fn generate_seed() -> u64 {
    let now = SystemTime::now().duration_since(UNIX_EPOCH).unwrap();
    now.as_secs() ^ ((now.subsec_nanos() as u64) << 32)
}

pub fn parse_duration_range(s: &str) -> Result<RangeInclusive<Duration>, String> {
    let (start, end) = s.split_once("..").ok_or_else(|| "expected MIN..MAX".to_string())?;
    let start = parse_duration(start)?;
    let end = parse_duration(end)?;
    if start > end {
        return Err("range start must be <= range end".to_string());
    }
    Ok(start..=end)
}

pub fn parse_duration(s: &str) -> Result<Duration, String> {
    let trimmed = s.trim();
    if let Ok(seconds) = trimmed.parse::<f64>() {
        if !seconds.is_finite() || seconds < 0.0 {
            return Err("duration must be finite and non-negative".to_string());
        }
        return Ok(Duration::seconds_f64(seconds));
    }
    let parsed = parse_time(trimmed).map_err(|e| e.to_string())?;
    if parsed.is_negative() {
        return Err("duration must be finite and non-negative".to_string());
    }
    Ok(parsed)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn is_prime_handles_small_boundaries() {
        assert!(!is_prime(0_u16));
        assert!(!is_prime(1_u16));
        assert!(is_prime(2_u16));
        assert!(is_prime(3_u16));
        assert!(!is_prime(4_u16));
    }

    #[test]
    fn is_prime_matches_known_small_values() {
        let known_primes = [5_u16, 7, 11, 13, 17, 19, 23, 97, 101];
        for value in known_primes {
            assert!(is_prime(value), "expected {value} to be prime");
        }

        let known_composites = [6_u16, 8, 9, 10, 12, 15, 21, 25, 100];
        for value in known_composites {
            assert!(!is_prime(value), "expected {value} to be composite");
        }
    }

    #[test]
    fn is_prime_handles_large_u16_values() {
        assert!(is_prime(65_521_u16)); // Largest prime representable in u16.
        assert!(!is_prime(65_535_u16));
        assert!(!is_prime(65_534_u16));
    }

    #[test]
    fn is_prime_behaves_consistently_across_unsigned_types() {
        assert_eq!(is_prime(251_u8), is_prime(251_u16));
        assert_eq!(is_prime(251_u8), is_prime(251_u32));
        assert_eq!(is_prime(252_u8), is_prime(252_u16));
        assert_eq!(is_prime(252_u8), is_prime(252_u32));
    }

    #[test]
    fn parse_duration_accepts_fractional_seconds() {
        assert_eq!(Duration::milliseconds(125), parse_duration("0.125").unwrap());
        assert!(parse_duration("-1").is_err());
        assert!(parse_duration("nan").is_err());
    }

    #[test]
    fn parse_duration_accepts_human_units() {
        assert_eq!(Duration::seconds(123), parse_duration("123s").unwrap());
        assert_eq!(Duration::seconds(123), parse_duration("123").unwrap());
        assert_eq!(Duration::milliseconds(125), parse_duration("125ms").unwrap());
        assert_eq!(Duration::seconds(62), parse_duration("1m2s").unwrap());
    }

    #[test]
    fn parse_duration_accepts_time_display_output() {
        let rendered = Duration::seconds(62).to_string(); // "1m2s"
        assert_eq!(Duration::seconds(62), parse_duration(&rendered).unwrap());
    }

    #[test]
    fn parse_duration_range_requires_ordered_bounds() {
        let range = parse_duration_range("0.25..1.5").unwrap();
        assert_eq!(Duration::milliseconds(250), *range.start());
        assert_eq!(Duration::milliseconds(1500), *range.end());
        assert!(parse_duration_range("2..1").is_err());
    }

    #[test]
    fn parse_duration_range_accepts_human_units() {
        let range = parse_duration_range("125ms..1m2s").unwrap();
        assert_eq!(Duration::milliseconds(125), *range.start());
        assert_eq!(Duration::seconds(62), *range.end());
    }
}
