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
