//! Small utilities for the transfer-matrix Phase 4 module.
//! Currently just a reduced rational fraction type.

use std::fmt;

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct Frac {
    pub num: i64,
    pub den: i64,
}

impl Frac {
    pub fn new(num: i64, den: i64) -> Self {
        assert!(den != 0, "Frac denominator must be nonzero");
        let mut n = num;
        let mut d = den;
        if d < 0 {
            n = -n;
            d = -d;
        }
        let g = gcd(n.unsigned_abs() as i64, d);
        let g = if g == 0 { 1 } else { g };
        Frac {
            num: n / g,
            den: d / g,
        }
    }
    pub fn as_f64(&self) -> f64 {
        self.num as f64 / self.den as f64
    }
}

impl fmt::Display for Frac {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.den == 1 {
            write!(f, "{}", self.num)
        } else {
            write!(f, "{}/{}", self.num, self.den)
        }
    }
}

fn gcd(a: i64, b: i64) -> i64 {
    let mut x = a.abs();
    let mut y = b.abs();
    while y != 0 {
        let t = y;
        y = x % y;
        x = t;
    }
    x
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn reduces() {
        assert_eq!(Frac::new(4, 2), Frac { num: 2, den: 1 });
        assert_eq!(Frac::new(-6, 9), Frac { num: -2, den: 3 });
        assert_eq!(Frac::new(0, 5), Frac { num: 0, den: 1 });
    }
}
