//! Motif extraction from optimal witness trees.
//!
//! Given an optimal spanning tree of an m × n grid (produced by
//! `witness::solve_with_witness`), decompose its edges into per-column
//! "fill patterns" and detect the periodic motif in the interior.
//!
//! For column c (0 ≤ c < n), the fill pattern is the pair
//!   * `v[c] : Vec<bool>` of length m-1 — whether the vertical edge
//!     between (r, c) and (r+1, c) is present, for r = 0..m-1.
//!   * `h[c] : Vec<bool>` of length m — whether the horizontal edge
//!     between (r, c) and (r, c+1) is present, for r = 0..m. (`h[n-1]`
//!     is empty / all false.)
//!
//! A *motif* is a contiguous run of column-fill patterns that repeats
//! exactly. We report:
//!   * The smallest period `q` such that `(v[c], h[c]) = (v[c+q], h[c+q])`
//!     for every c in some long-enough window of interior columns.
//!   * The motif itself (one period worth of column fills).
//!   * The "boundary transient" before and after the periodic core.

use crate::witness;

#[cfg(test)]
mod tests {
    use super::*;

    /// Gain-sequence period detection on optimal witnesses recovers the
    /// rational alpha_m from analysis/recurrences.md for m ∈ {3..8}.
    /// We use n large enough to expose at least 2 full periods of the
    /// known q_m, plus the m₀ burn-in.
    #[test]
    fn gain_period_matches_recurrences_md() {
        // (m, n, expected alpha numerator, expected alpha denominator)
        // n picked to comfortably cover ≥ 2 full periods past the burn-in:
        //   m=3 q=3 n0=3:  n=20 gives ~5 periods after burn-in
        //   m=4 q=1 n0=3:  any n ≥ 6
        //   m=5 q=3 n0=4:  n=20
        //   m=6 q=2 n0=10: n=22
        //   m=7 q=1 n0=7:  any n ≥ 14
        //   m=8 q=7 n0=13: need ≥ 13 + 2*7 = 27, take n=35 for safety
        let cases = [
            (3usize, 20usize, 4i64, 3i64),
            (4, 14, 2, 1),
            (5, 20, 2, 1),
            (6, 24, 5, 2),
            (7, 18, 3, 1),
            (8, 35, 22, 7),
        ];
        for &(m, n, en, ed) in &cases {
            let w = witness::solve_with_witness(m, n).expect("non-empty");
            let gains = extract_per_column_gains(&w);
            let qmax = 12usize;
            let skip = std::cmp::max(2, w.m);
            let (q, _s, _e) = detect_period_in_seq(&gains, qmax, skip, 2)
                .unwrap_or_else(|| panic!("no period detected at m={m} n={n}"));
            let motif: Vec<u32> = gains[_s..(_s + q)].to_vec();
            let motif_sum: i64 = motif.iter().map(|&x| x as i64).sum();
            // Reduce motif_sum / q.
            let gd = {
                let (mut a, mut b) = (motif_sum, q as i64);
                while b != 0 {
                    let t = b;
                    b = a % b;
                    a = t;
                }
                a.max(1)
            };
            let num = motif_sum / gd;
            let den = (q as i64) / gd;
            // Equality of reduced fractions:
            assert_eq!(
                (num, den),
                (en, ed),
                "alpha mismatch at m={m} n={n}: got {}/{} expected {}/{}",
                num,
                den,
                en,
                ed
            );
        }
    }
}

/// Per-column fill pattern.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ColumnPattern {
    /// Vertical edges within this column. Length m-1.
    /// `vert[r] = true` iff the edge (r, c)-(r+1, c) is in the tree.
    pub vert: Vec<bool>,
    /// Horizontal edges leaving this column to the right.
    /// Length m. `horiz[r] = true` iff the edge (r, c)-(r, c+1) is in the
    /// tree. For c = n-1, all entries are false.
    pub horiz: Vec<bool>,
}

impl ColumnPattern {
    /// Pretty-print as a 2-row string: vertical pattern (m-1 chars) and
    /// horizontal pattern (m chars), separated by '|'.
    pub fn fmt_compact(&self) -> String {
        let v: String = self
            .vert
            .iter()
            .map(|&b| if b { '|' } else { '.' })
            .collect();
        let h: String = self
            .horiz
            .iter()
            .map(|&b| if b { '-' } else { '.' })
            .collect();
        format!("v={} h={}", v, h)
    }
}

/// Extract per-column patterns from the witness's edge list. The witness
/// is assumed to be in canonical (m ≤ n) frame.
pub fn extract_patterns(w: &witness::Witness) -> Vec<ColumnPattern> {
    let m = w.m;
    let n = w.n;
    let mut cols: Vec<ColumnPattern> = (0..n)
        .map(|_| ColumnPattern {
            vert: vec![false; m.saturating_sub(1)],
            horiz: vec![false; m],
        })
        .collect();
    for &((r1, c1), (r2, c2)) in &w.edges {
        if c1 == c2 && r2 == r1 + 1 {
            // vertical within column c1
            cols[c1].vert[r1] = true;
        } else if r1 == r2 && c2 == c1 + 1 {
            // horizontal from c1 to c1+1
            cols[c1].horiz[r1] = true;
        } else {
            // edges are stored with (r1,c1) <= (r2,c2), so this branch
            // shouldn't trigger for grid edges; but be defensive.
            panic!("non-grid or unsorted edge: ({r1},{c1})-({r2},{c2})");
        }
    }
    cols
}

/// Find the smallest period q ∈ 1..=qmax such that there's a window of
/// at least `min_window` consecutive interior columns where the pattern
/// satisfies `cols[c] == cols[c + q]`. Returns (period, window_start,
/// window_end_exclusive) on success.
///
/// We restrict to "interior" columns, namely c ∈ skip..(n - skip), to
/// ignore boundary effects. We try q = 1, 2, ..., qmax in order and pick
/// the first that gives a window of length ≥ min_window.
pub fn detect_period(
    cols: &[ColumnPattern],
    qmax: usize,
    skip: usize,
    min_window: usize,
) -> Option<(usize, usize, usize)> {
    let n = cols.len();
    if n < 2 * skip + min_window {
        return None;
    }
    for q in 1..=qmax {
        // Find longest run of indices c in skip..(n - skip - q) with
        // cols[c] == cols[c + q]. Take the longest one.
        let mut best_start = None;
        let mut best_len = 0usize;
        let mut cur_start = None;
        let mut cur_len = 0usize;
        for c in skip..(n.saturating_sub(skip + q)) {
            if cols[c] == cols[c + q] {
                if cur_start.is_none() {
                    cur_start = Some(c);
                    cur_len = 0;
                }
                cur_len += 1;
                if cur_len > best_len {
                    best_len = cur_len;
                    best_start = cur_start;
                }
            } else {
                cur_start = None;
                cur_len = 0;
            }
        }
        if best_len >= min_window {
            // The window where cols[c..c+q*k] is q-periodic spans
            // best_start .. best_start + best_len + q  (since the
            // condition cols[c] = cols[c+q] holding for c in [s, s+L)
            // means the window covers columns s..(s+L+q)).
            let start = best_start.unwrap();
            let end = start + best_len + q;
            return Some((q, start, end.min(n)));
        }
    }
    None
}

/// Compute per-column gains: for each column c in [0, n), count the
/// vertices (r, c) whose tree-degree equals their grid-degree.
pub fn extract_per_column_gains(w: &witness::Witness) -> Vec<u32> {
    let m = w.m;
    let n = w.n;
    let mut deg = vec![0u32; m * n];
    for &((r1, c1), (r2, c2)) in &w.edges {
        deg[r1 * n + c1] += 1;
        deg[r2 * n + c2] += 1;
    }
    let grid_deg = |r: usize, c: usize| -> u32 {
        let up = if r > 0 { 1 } else { 0 };
        let dn = if r + 1 < m { 1 } else { 0 };
        let lf = if c > 0 { 1 } else { 0 };
        let rt = if c + 1 < n { 1 } else { 0 };
        up + dn + lf + rt
    };
    (0..n)
        .map(|c| {
            let mut g = 0u32;
            for r in 0..m {
                if deg[r * n + c] == grid_deg(r, c) {
                    g += 1;
                }
            }
            g
        })
        .collect()
}

/// Detect the smallest period q ∈ 1..=qmax in a numeric sequence such
/// that the *entire interior window* `seq[skip..(n - skip)]` is exactly
/// q-periodic (i.e. seq[c] = seq[c + q] for every c in that window with
/// c + q within the window). Returns (q, window_start, window_end).
///
/// We require at least min_repeats full periods inside the window before
/// accepting. This is robust to local "false-positive" sub-periods like
/// q=1 inside a {3,3,3,...,4,3,3,...} sequence.
pub fn detect_period_in_seq(
    seq: &[u32],
    qmax: usize,
    skip: usize,
    min_repeats: usize,
) -> Option<(usize, usize, usize)> {
    let n = seq.len();
    if n < 2 * skip {
        return None;
    }
    let interior_start = skip;
    let interior_end = n - skip;
    if interior_end <= interior_start {
        return None;
    }
    let interior_len = interior_end - interior_start;
    for q in 1..=qmax {
        if interior_len < min_repeats * q + 1 {
            continue;
        }
        // Check seq[c] == seq[c + q] for every c in [interior_start, interior_end - q).
        let mut ok = true;
        for c in interior_start..(interior_end - q) {
            if seq[c] != seq[c + q] {
                ok = false;
                break;
            }
        }
        if ok {
            return Some((q, interior_start, interior_end));
        }
    }
    None
}

/// High-level helper: solve, extract patterns, detect period, report.
/// Returns a printable summary.
pub fn analyze(m: usize, n: usize) -> String {
    let mut out = String::new();
    let w = match witness::solve_with_witness(m, n) {
        Some(w) => w,
        None => return format!("# empty grid m={m} n={n}\n"),
    };
    let cols = extract_patterns(&w);
    out.push_str(&format!(
        "# m={} n={} value={} edges={}\n",
        w.m,
        w.n,
        w.value,
        w.edges.len()
    ));
    if w.transposed {
        out.push_str(&format!(
            "# (note: input was {}x{}, working in transposed canonical frame {}x{})\n",
            n, m, w.m, w.n
        ));
    }
    // ASCII visualization.
    out.push_str("# spanning-tree visualization (each block = one column):\n");
    let m_eff = w.m;
    let n_eff = w.n;
    for r in 0..m_eff {
        let mut line = String::new();
        for c in 0..n_eff {
            line.push('o');
            if c + 1 < n_eff {
                line.push(if cols[c].horiz[r] { '-' } else { ' ' });
            }
        }
        out.push_str(&line);
        out.push('\n');
        if r + 1 < m_eff {
            let mut vline = String::new();
            for c in 0..n_eff {
                vline.push(if cols[c].vert[r] { '|' } else { ' ' });
                if c + 1 < n_eff {
                    vline.push(' ');
                }
            }
            out.push_str(&vline);
            out.push('\n');
        }
    }
    out.push('\n');

    // -- Per-column gain analysis (the rigorous, tie-break-invariant
    //    quantity).
    let gains = extract_per_column_gains(&w);
    out.push_str("# per-column full-degree counts (gain sequence):\n#  ");
    for (c, &g) in gains.iter().enumerate() {
        if c > 0 && c % 14 == 0 {
            out.push_str("\n#  ");
        }
        out.push_str(&format!("{:2} ", g));
    }
    out.push('\n');

    let qmax = 12usize;
    let skip = std::cmp::max(2, m_eff);
    let min_repeats = 2usize;
    if let Some((q, s, e)) = detect_period_in_seq(&gains, qmax, skip, min_repeats) {
        let motif: Vec<u32> = gains[s..s + q].to_vec();
        let motif_sum: u32 = motif.iter().sum();
        out.push_str(&format!(
            "# gain-sequence period: q={} on window [{}..{}) (length {})\n",
            q,
            s,
            e,
            e - s
        ));
        out.push_str(&format!(
            "# gain motif: {:?} (sum {} over {} columns) => alpha = {}/{}\n",
            motif, motif_sum, q, motif_sum, q
        ));
        // Also report the gcd-reduced rational.
        let gd = {
            let (mut a, mut b) = (motif_sum as i64, q as i64);
            while b != 0 {
                let t = b;
                b = a % b;
                a = t;
            }
            a.max(1)
        };
        out.push_str(&format!(
            "# alpha (reduced) = {}/{}\n",
            (motif_sum as i64) / gd,
            (q as i64) / gd
        ));
    } else {
        out.push_str("# no period detected in gain sequence (within q ≤ 12)\n");
    }

    // -- Per-column edge-pattern period (informational; less reliable
    //    due to DP tie-breaking).
    if let Some((q, s, e)) = detect_period(&cols, qmax, skip, std::cmp::max(2, qmax)) {
        out.push_str(&format!(
            "# edge-pattern period: q={} on window [{}..{}) (length {})\n",
            q,
            s,
            e,
            e - s
        ));
        for off in 0..q {
            let c = s + off;
            out.push_str(&format!("#   col[{}] {}\n", c, cols[c].fmt_compact()));
        }
    } else {
        out.push_str(
            "# no edge-pattern period detected (DP tie-breaking can scramble equal-value motifs)\n",
        );
    }
    out
}
