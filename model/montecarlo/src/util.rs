use duration_str::parse_time;
use lowcharts::plot;
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

/// Given a base seed and an index, derives a new seed that is deterministic but well-diffused.
pub fn derive_seed(base_seed: u64, index: usize) -> u64 {
    // splitmix64: deterministic diffusion from the base seed and run index.
    let mut x = base_seed.wrapping_add((index as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15));
    x = (x ^ (x >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    x = (x ^ (x >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    x ^ (x >> 31)
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

pub fn worker_count() -> usize {
    std::thread::available_parallelism().map_or(1, |cpus| compute_worker_count_from_logical(cpus.get()))
}

fn compute_worker_count_from_logical(logical: usize) -> usize {
    logical.saturating_sub(1).max(1)
}

#[derive(Debug, Clone, Copy)]
pub struct TimeStats {
    pub min: f64,
    pub mean: f64,
    pub median: f64,
    pub max: f64,
}

impl TimeStats {
    pub fn compute(times: &[Duration]) -> Option<TimeStats> {
        if times.is_empty() {
            return None;
        }
        let mut values = times.iter().map(|time| time.as_seconds_f64()).collect::<Vec<_>>();
        values.sort_by(|a, b| a.total_cmp(b));

        let min = values[0];
        let max = values[values.len() - 1];
        let sum: f64 = values.iter().sum();
        let mean = sum / (values.len() as f64);
        let mid = values.len() / 2;
        let median = if values.len() % 2 == 0 { (values[mid - 1] + values[mid]) * 0.5 } else { values[mid] };

        Some(TimeStats { min, mean, median, max })
    }
}

pub fn print_convergence_histogram(time_samples: &[Duration]) {
    if time_samples.is_empty() {
        return;
    }
    let times_f64: Vec<f64> = time_samples.iter().map(|t| t.as_seconds_f64()).collect();

    // Round min/max to nearest second boundaries
    let min_seconds = times_f64.iter().cloned().fold(f64::INFINITY, f64::min).floor() as i32;
    let max_seconds = times_f64.iter().cloned().fold(0.0, f64::max).ceil() as i32;
    let span = (max_seconds - min_seconds) as usize;
    if span == 0 {
        eprintln!("Histogram: all values identical ({:.3} s)", times_f64[0]);
        return;
    }

    // Find smallest "nice" bin size [1, 2, 5, 10, 20, 50, ...] that gives >= 10 bins
    let nice_sizes = [1, 2, 5, 10, 20, 50, 100, 200, 500, 1000, 2000, 5000];
    let mut bin_size = 1;
    for size in nice_sizes.iter() {
        let num_bins = ((span as f64) / (*size as f64)).ceil() as usize;
        if num_bins >= 10 {
            bin_size = *size;
            break;
        }
    }
    let num_bins = ((span as f64) / (bin_size as f64)).ceil() as usize;

    // Display histogram with calculated bin count
    let options = plot::HistogramOptions { intervals: num_bins, ..Default::default() };
    let histogram = plot::Histogram::new(&times_f64, options);
    eprintln!("\n📊 CONVERGENCE TIME HISTOGRAM [s] ({} bins × {} s each)\n{}", num_bins, bin_size, histogram);
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

    #[test]
    fn summarize_times_handles_odd_and_even_lengths() {
        let odd = vec![Duration::seconds(1), Duration::seconds(3), Duration::seconds(2)];
        let odd_stats = TimeStats::compute(&odd).expect("stats should be present for odd vector");
        assert_eq!(1.0, odd_stats.min);
        assert_eq!(2.0, odd_stats.mean);
        assert_eq!(2.0, odd_stats.median);
        assert_eq!(3.0, odd_stats.max);

        let even = vec![Duration::seconds(1), Duration::seconds(4), Duration::seconds(2), Duration::seconds(3)];
        let even_stats = TimeStats::compute(&even).expect("stats should be present for even vector");
        assert_eq!(1.0, even_stats.min);
        assert_eq!(2.5, even_stats.mean);
        assert_eq!(2.5, even_stats.median);
        assert_eq!(4.0, even_stats.max);
    }

    #[test]
    fn summarize_times_returns_none_for_empty_input() {
        assert!(TimeStats::compute(&[]).is_none());
    }
}
