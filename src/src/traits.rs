use crypto_bigint::subtle::{Choice, ConstantTimeEq};

/// Multiplicative identity (unity).
pub trait One: ConstantTimeEq + Sized {
    /// Create an instance of the multiplicative identity (i.e. the value `1`)
    /// in the underlying algebraic structure.
    fn one() -> Self;

    /// Determine if this value is the multiplicative identity (i.e. `Self::one`)
    /// in the underlying algebraic structure.
    /// If so, returns `Choice(1)`. Otherwise, returns `Choice(0)`.
    #[inline]
    fn is_one(&self) -> Choice {
        self.ct_eq(&Self::one())
    }

    /// Set `self` to the multiplicative identity (i.e. `Self::one`)
    /// in the underlying algebraic structure.
    #[inline]
    fn set_one(&mut self) {
        *self = One::one();
    }

    /// Return the value `1` in the same algebraic structure as `other`.
    fn one_like(other: &Self) -> Self where Self: Clone {
        let mut ret = other.clone();
        ret.set_one();
        ret
    }
}

pub trait BNField {

    /// Convert `self` to byte array representation.
    fn to_bytes(&self) -> Vec<u8>;

    /// Compute the value of 2&times;`self`.
    fn double(&self) -> Self;

    /// Compute the value of `self`/2.
    fn half(&self) -> Self;

    /// Compute `self`&sup2;.
    fn sq(&self) -> Self;

    /// Compute `self`&sup3;.
    fn cb(&self) -> Self;

    /// Compute the inverse of `self` (or 0, if `self` itself is zero).
    fn inv(&self) -> Self;
}
