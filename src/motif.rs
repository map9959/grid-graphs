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
        let v: String = self.vert.iter().map(|&b| if b { '|' } else { '.' }).collect();
        let h: String = self.horiz.iter().map(|&b| if b { '-' } else { '.' }).collect();
        format!("v={} h={}", v, h)
    }
}

/// Extract per-column patterns from the witness's edge list. The witness
/// is assumed to be in canonical (m ≤ n) frame.
pub fn extract_patterns(w: &witness::Witness) -> Vec<ColumnPattern> {
    let m = w.m;
    let n = w.n;
    let mut cols: Vec<ColumnPattern> = (0..n).map(|_| ColumnPattern {
        vert: vec![false; m.saturating_sub(1)],
        horiz: vec![false; m],
    }).collect();
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
    if n < 2 * skip + min_window { return None; }
    for q in 1..=qmax {
        // Find longest run of indices c in skip..(n - skip - q) with
        // cols[c] == cols[c + q]. Take the longest one.
        let mut best_start = None;
        let mut best_len = 0usize;
        let mut cur_start = None;
        let mut cur_len = 0usize;
        for c in skip..(n.saturating_sub(skip + q)) {
            if cols[c] == cols[c + q] {
                if cur_start.is_none() { cur_start = Some(c); cur_len = 0; }
                cur_len += 1;
                if cur_len > best_len { best_len = cur_len; best_start = cur_start; }
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

/// High-level helper: solve, extract patterns, detect period, report.
/// Returns a printable summary.
pub fn analyze(m: usize, n: usize) -> String {
    let mut out = String::new();
    let w = match witness::solve_with_witness(m, n) {
        Some(w) => w,
        None => return format!("# empty grid m={m} n={n}\n"),
    };
    let cols = extract_patterns(&w);
    out.push_str(&format!("# m={} n={} value={} edges={}\n", w.m, w.n, w.value, w.edges.len()));
    // Per-column dump (transpose-aware).
    if w.transposed {
        out.push_str(&format!("# (note: input was {}x{}, working in transposed canonical frame {}x{})\n",
                              n, m, w.m, w.n));
    }
    // Show a compact ASCII grid: m rows × n columns of vertices, with
    // vertical edges between rows, horizontal edges between columns.
    out.push_str("# spanning-tree visualization (each block = one column):\n");
    let m_eff = w.m;
    let n_eff = w.n;
    // For each row of vertices, print the row vertices and the horizontal
    // edge to the next column. Then between rows, print the vertical
    // edges within each column.
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
                if c + 1 < n_eff { vline.push(' '); }
            }
            out.push_str(&vline);
            out.push('\n');
        }
    }
    out.push('\n');
    // Periodicity detection.
    let qmax = 12usize;
    let skip = std::cmp::max(2, m_eff);
    let min_window = std::cmp::max(2, qmax);
    if let Some((q, s, e)) = detect_period(&cols, qmax, skip, min_window) {
        out.push_str(&format!(
            "# detected period q={} on column window [{}..{}) (length {})\n",
            q, s, e, e - s
        ));
        out.push_str(&format!("# motif (one period, columns {}..{}):\n", s, s + q));
        for off in 0..q {
            let c = s + off;
            out.push_str(&format!("#   col[{}] {}\n", c, cols[c].fmt_compact()));
        }
        // Average gain per period: count full-degree vertices in columns
        // [s, s+q) (which are interior since s ≥ skip ≥ m_eff). For each
        // such vertex, full-degree means tree-degree == grid-degree.
        // We compute degrees from the witness edges by scanning.
        let mut deg = vec![0u32; m_eff * n_eff];
        for &((r1, c1), (r2, c2)) in &w.edges {
            deg[r1 * n_eff + c1] += 1;
            deg[r2 * n_eff + c2] += 1;
        }
        let interior_target = |r: usize, _c: usize| -> u32 {
            if r == 0 || r + 1 == m_eff { 3 } else { 4 }
        };
        let mut motif_full = 0u32;
        for off in 0..q {
            let c = s + off;
            for r in 0..m_eff {
                if deg[r * n_eff + c] == interior_target(r, c) { motif_full += 1; }
            }
        }
        out.push_str(&format!(
            "# motif gain per period = {} full-degree vertices over {} columns => alpha = {}/{}\n",
            motif_full, q, motif_full, q
        ));
    } else {
        out.push_str("# no period detected (within q ≤ 12)\n");
    }
    out
}
