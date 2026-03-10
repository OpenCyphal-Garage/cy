use num_traits::{PrimInt, Unsigned};

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

#[cfg(test)]
mod tests {
    use super::is_prime;

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
}
