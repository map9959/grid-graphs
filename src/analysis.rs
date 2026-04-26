//! Analytical helper routines for P(m,n): the maximum number of fully-preserved
//! (original-degree-equal) vertices in a spanning tree of the m×n grid.
//!
//! The dynamic programming in `main.rs` gives exact values for moderate widths.
//! These functions supply *conservative* bounds used for comparison / sanity checks.
//!
//! Implemented:
//!  - `upper_bound` (capacity / deficiency packing):  mn - ceil( 2(m-1)(n-1) / 3 )  (provable)
//!  - `upper_bound_relaxed` (adds square hitting + capacity mix; may tighten `upper_bound`)
//!  - `upper_bound_refined` (piecewise thin-grid refinement matching DERIVATION.md Section 2)
//!  - `lower_bound_simple` = max(m,n)  (provable, matches exact for all 1×n and 2×n tested)
//!  - `lower_bound_band`   conservative band heuristic: max of simple bound and (preserve every
//!        other row or column) minus a safety margin to avoid overshoot on small grids.
//!
//! NOTE: Earlier drafts used m + n - 1 as a "simple lower bound"; that was not uniformly
//! valid for all instances considered here, so it has been replaced with max(m,n).
//! The band lower bound includes a subtractive margin (min(m,n)) precisely because a naive
//! (m/2)*n claim exceeded actual optima for small m (e.g. 3×6). Adjust margin only after
//! enlarging the empirical validation set.
//!
//! See `docs/DERIVATION.md` for the theoretical background; that document may mention
//! stronger *candidate* constructions—only the conservative forms are encoded here.

/// Integer ceiling division helper.
#[inline]
const fn ceil_div(a: u64, b: u64) -> u64 {
    (a + b - 1) / b
}

/// Upper bound: mn - ceil( 2(m-1)(n-1) / 3 ).
pub fn upper_bound(m: usize, n: usize) -> usize {
    if m == 0 || n == 0 {
        return 0;
    }
    let m1 = m as u64 - 1;
    let n1 = n as u64 - 1;
    let d = 2 * m1 * n1; // total deficiency
    let need = ceil_div(d, 3); // minimum non-preserved vertices if each carried 3 deficiency
    m * n - need as usize
}

/// Refined piecewise upper bound (DERIVATION.md):
/// Let D = 2(m-1)(n-1), I = (m-2)(n-2) (interior count; 0 if m<3 or n<3).
/// If D <= 3I, same as basic capacity bound.
/// Else all interiors are saturated (def=3) and residual R = D-3I is absorbed on border
/// with capacity at most 2 per vertex => need I + ceil(R/2) non-preserved vertices.
/// Returns value ≤ `upper_bound` (strictly smaller for thin grids satisfying mn < 4m+4n-10).
pub fn upper_bound_refined(m: usize, n: usize) -> usize {
    if m == 0 || n == 0 {
        return 0;
    }
    if m == 1 && n == 1 {
        return 1;
    }
    let (m1, n1) = (m as i64 - 1, n as i64 - 1);
    let d = 2 * m1 * n1; // total deficiency
                         // interior count
    let interior = if m >= 3 && n >= 3 {
        (m as i64 - 2) * (n as i64 - 2)
    } else {
        0
    };
    let three_i = 3 * interior;
    if d <= three_i {
        // falls back to basic bound
        return upper_bound(m, n);
    }
    // residual
    let r = d - three_i; // > 0
                         // need = I + ceil(r/2)
    let need_non_preserved = interior + (r + 1) / 2; // all integer math
    let p = (m as i64 * n as i64) - need_non_preserved;
    // safety: never exceed basic upper bound (numerical guard)
    let ub_basic = upper_bound(m, n) as i64;
    p.min(ub_basic).max(0) as usize
}

/// Simple safe lower bound (provable): at least all vertices of the larger dimension
/// can be preserved. This matches exact values for all tested 1×n and 2×n grids where
/// P(2,n) = n for n ≥ 2 and P(2,1)=2.
pub fn lower_bound_simple(m: usize, n: usize) -> usize {
    m.max(n)
}

/// A tighter theoretical lower bound could be inserted here later.
pub fn lower_bound(m: usize, n: usize) -> usize {
    lower_bound_simple(m, n)
}

/// Placeholder for a future verified band construction.
///
/// Earlier drafts returned a heuristic every-other-row estimate. Wider diagonal
/// data shows that estimate can exceed the best known values, so it is not a
/// valid lower bound. Until a construction is encoded and checked, keep this at
/// the simple safe bound.
pub fn lower_bound_band(m: usize, n: usize) -> usize {
    lower_bound_simple(m, n)
}

/// Relaxed upper bound mixing capacity and 2×2 square coverage constraints.
/// We approximate choosing a minimum set X of non-preserved vertices using only
/// aggregated counts of interior / edge / corner vertices:
///   - Total deficiency constraint: Σ cap(v) ≥ 2(m-1)(n-1).
///   - Square hitting surrogate: 4*k_i + 2*k_e + k_c ≥ (m-1)(n-1).
/// Greedy fill with interiors first (best joint ratio), then edges/corners.
/// Produces a number ≤ `upper_bound` or equal when interior supply is large.
pub fn upper_bound_relaxed(m: usize, n: usize) -> usize {
    if m == 0 || n == 0 {
        return 0;
    }
    let s = (m - 1) * (n - 1); // squares
    let d = 2 * s; // deficiency
    let interiors = if m >= 2 && n >= 2 {
        (m - 2) * (n - 2)
    } else {
        0
    };
    // Need k_i >= max( ceil(2s/3), ceil(s/4) ). Since 2s/3 >= s/4, just ceil(2s/3).
    let need_interiors = (2 * s + 2) / 3; // ceil(2s/3)
    if interiors >= need_interiors {
        let k = need_interiors; // all served by interiors
        return m * n - k;
    }
    // Use all interiors, residual constraints.
    let k_i = interiors;
    let cover_used = 4 * k_i; // covered squares
    let cap_used = 3 * k_i; // deficiency covered
    let s_rem = s.saturating_sub(cover_used);
    let d_rem = d.saturating_sub(cap_used);
    // Remaining vertices will be edges/corners with coverage=capacity ratio 1 or 2/2.
    // Edges have (2,2), corners (1,1); both same ratio, prefer edges.
    // Need 2*k_e + k_c >= max(s_rem, d_rem). Minimal extra vertices = ceil(max/2).
    let need = s_rem.max(d_rem);
    let extra = (need + 1) / 2; // ceil(need/2)
    let k_total = k_i + extra;
    m * n - k_total
}

#[cfg(test)]
mod tests {
    use super::*;
    // bring solve for empirical verification
    use crate::solve;
    #[test]
    fn trivial_bounds_hold_small() {
        for m in 1..=8 {
            for n in 1..=8 {
                let lb = lower_bound(m, n);
                let ub = upper_bound(m, n);
                assert!(lb <= ub, "bounds inverted for {m}x{n}: lb={lb} ub={ub}");
            }
        }
    }
    #[test]
    fn refined_never_worse_and_valid() {
        // Limit to 9x9 for test-time performance; larger instances (>=10) are slower.
        for m in 1..=9 {
            for n in 1..=9 {
                let act = solve(m, n, None, false) as usize;
                let ub_basic = upper_bound(m, n);
                let ub_ref = upper_bound_refined(m, n);
                assert!(
                    ub_ref <= ub_basic,
                    "refined exceeds basic for {m}x{n}: refined={ub_ref} basic={ub_basic}"
                );
                assert!(
                    act <= ub_ref,
                    "refined upper bound violated for {m}x{n}: act={act} ref={ub_ref}"
                );
            }
        }
    }
    #[test]
    fn refined_expected_4xn_pattern() {
        // For m=4, derivation predicts refined = 2n+1 (n>=2) while basic = 2n+2.
        for n in 2..=10 {
            let r = upper_bound_refined(4, n);
            assert_eq!(r, 2 * n + 1, "unexpected refined bound for 4x{n}: got {r}");
            let b = upper_bound(4, n);
            assert_eq!(b, 2 * n + 2, "unexpected basic bound for 4x{n}: got {b}");
        }
    }
    #[test]
    fn monotonicity() {
        for m in 1..=10 {
            for n in 1..=10 {
                if n > 1 {
                    assert!(upper_bound(m, n) >= upper_bound(m, n - 1));
                }
                if m > 1 {
                    assert!(upper_bound(m, n) >= upper_bound(m - 1, n));
                }
            }
        }
    }
    #[test]
    fn lower_bounds_valid_small() {
        for m in 1..=6 {
            for n in 1..=10 {
                let act = solve(m, n, None, false);
                assert!(
                    lower_bound_simple(m, n) as i32 <= act,
                    "LB_simple too high for {m}x{n}: lb={} act={}",
                    lower_bound_simple(m, n),
                    act
                );
                assert!(
                    lower_bound_band(m, n) as i32 <= act,
                    "LB_band too high for {m}x{n}: lb={} act={}",
                    lower_bound_band(m, n),
                    act
                );
            }
        }
        for m in 1..=10 {
            for n in 1..=6 {
                let act = solve(m, n, None, false);
                assert!(
                    lower_bound_simple(m, n) as i32 <= act,
                    "LB_simple too high for {m}x{n}: lb={} act={}",
                    lower_bound_simple(m, n),
                    act
                );
                assert!(
                    lower_bound_band(m, n) as i32 <= act,
                    "LB_band too high for {m}x{n}: lb={} act={}",
                    lower_bound_band(m, n),
                    act
                );
            }
        }
    }
}
