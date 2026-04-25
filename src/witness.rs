//! Witness-recording variant of the frontier DP.
//!
//! `solve_with_witness(m, n)` returns the optimal full-degree count *and* an
//! explicit spanning-tree edge set achieving it. The DP mirrors the structure
//! of `solve` in `main.rs` but stores per-cell predecessor pointers so we can
//! back-trace one optimal path through the DAG of frontier states after the
//! forward sweep completes.
//!
//! Operates in the canonical (m ≤ n) frame: if the user passes `m > n`, the
//! function transposes internally and emits edges in the swapped frame.
//! Callers that need the user-frame edges should swap each (r, c) ↔ (c, r)
//! after calling.
//!
//! Pruning: this variant deliberately turns off both the budget-based
//! `prune` flag and beam pruning, to guarantee that the recovered tree is
//! genuinely optimal.

use hashbrown::HashMap;
use std::hash::{BuildHasherDefault, Hasher};

const MAX_M: usize = 16;

#[inline] fn get4(x: u64, i: usize) -> u8 { ((x >> (i * 4)) & 0xF) as u8 }
#[inline] fn set4(x: &mut u64, i: usize, v: u8) {
    let s = i * 4;
    *x = (*x & !(0xFu64 << s)) | ((v as u64) << s);
}
#[inline] fn get2(x: u32, i: usize) -> u8 { ((x >> (i * 2)) & 0x3) as u8 }
#[inline] fn set2(x: &mut u32, i: usize, v: u8) {
    let s = i * 2;
    *x = (*x & !(0x3u32 << s)) | ((v as u32) << s);
}

#[derive(Clone, Copy, Eq, PartialEq, Debug)]
struct Key {
    labels: u64,
    degs: u32,
    ecount: u16,
}

impl std::hash::Hash for Key {
    #[inline(always)]
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u64(self.labels);
        let tail = (self.degs as u64) | ((self.ecount as u64) << 32);
        state.write_u64(tail);
    }
}

#[derive(Default)]
struct KHasher(u64);
impl Hasher for KHasher {
    #[inline(always)] fn write(&mut self, bytes: &[u8]) {
        let mut h = self.0;
        for &b in bytes { h = h.rotate_left(5) ^ b as u64 * 0x517cc1b727220a95; }
        self.0 = h;
    }
    #[inline(always)] fn write_u64(&mut self, i: u64) {
        let mut x = i ^ 0x9e3779b97f4a7c15;
        x = (x ^ (x >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
        x = (x ^ (x >> 27)).wrapping_mul(0x94d049bb133111eb);
        self.0 ^= x;
    }
    #[inline(always)] fn finish(&self) -> u64 { self.0 }
}
type FastBuild = BuildHasherDefault<KHasher>;

#[inline]
fn grid_deg(m: usize, n: usize, r: usize, c: usize) -> u8 {
    let up = (r > 0) as u8;
    let dn = (r + 1 < m) as u8;
    let lf = (c > 0) as u8;
    let rt = (c + 1 < n) as u8;
    up + dn + lf + rt
}

#[inline]
fn comp_present(labels: u64, m: usize, comp: u8) -> bool {
    for i in 0..m { if get4(labels, i) == comp { return true; } }
    false
}

#[inline]
fn merge_labels(labels: &mut u64, m: usize, a: u8, b: u8) {
    if a == 0 || b == 0 || a == b { return; }
    for i in 0..m {
        if get4(*labels, i) == b { set4(labels, i, a); }
    }
}

#[inline]
fn canonicalize(labels: &mut u64, m: usize) {
    let mut map = [0u8; 16];
    let mut next: u8 = 1;
    let mut new_labels: u64 = 0;
    for i in 0..m {
        let id = get4(*labels, i);
        if id == 0 { continue; }
        let slot = map[id as usize];
        let nid = if slot == 0 {
            let v = next; next += 1; map[id as usize] = v; v
        } else { slot };
        set4(&mut new_labels, i, nid);
    }
    *labels = new_labels;
}

#[inline]
fn is_canonical(labels: u64, m: usize) -> bool {
    let mut bit: u32 = 0;
    let mut max_id = 0u8;
    for i in 0..m {
        let id = get4(labels, i);
        if id == 0 { continue; }
        bit |= 1u32 << id;
        if id > max_id { max_id = id; }
    }
    if max_id == 0 { return true; }
    let needed = ((1u32 << (max_id + 1)) - 2) & !1;
    (bit & needed) == needed && bit.count_ones() as u8 == max_id
}

/// Predecessor record: from which Key in the previous cell-layer this state
/// was reached, and which (x, y) decision was made at that cell.
#[derive(Clone, Copy, Debug)]
struct Pred {
    prev_key: Key,
    x: u8,
    y: u8,
}

/// An edge of the grid graph in the canonical (m ≤ n) frame.
/// Each edge is `((r1, c1), (r2, c2))` with `(r1, c1) < (r2, c2)` lexicographically.
pub type Edge = ((usize, usize), (usize, usize));

/// Result of an optimal-witness solve.
pub struct Witness {
    pub m: usize,
    pub n: usize,
    pub transposed: bool,    // true if the original (m, n) was swapped to enforce m ≤ n
    pub value: i32,           // optimal full-degree count
    pub edges: Vec<Edge>,     // m·n − 1 edges of an optimal spanning tree (canonical frame)
}

/// Backtracking solver. Returns Some(witness) on success; None for the
/// degenerate empty grid.
pub fn solve_with_witness(m_user: usize, n_user: usize) -> Option<Witness> {
    if m_user == 0 || n_user == 0 { return None; }
    if m_user == 1 && n_user == 1 {
        return Some(Witness { m: 1, n: 1, transposed: false, value: 1, edges: vec![] });
    }
    let (mut m, mut n) = (m_user, n_user);
    let transposed = m > n;
    if transposed { std::mem::swap(&mut m, &mut n); }
    assert!(m <= MAX_M);

    // Per-cell tables of (Key -> (best value, predecessor)). One per cell, plus the
    // initial layer (before any cell is processed).
    // Index `t` runs 0..=pcount where pcount = m*n; t=0 is the initial frontier and
    // t=p_index+1 is "after processing cell with linear index p_index".
    let pcount = m * n;
    let mut layers: Vec<HashMap<Key, (i32, Option<Pred>), FastBuild>> = (0..=pcount)
        .map(|_| HashMap::with_hasher(FastBuild::default()))
        .collect();

    // Initial frontier: column 0 placeholder labels 1..=m, all degs 0.
    let mut labels0: u64 = 0;
    let mut degs0: u32 = 0;
    for r in 0..m {
        set4(&mut labels0, r, (r as u8) + 1);
        set2(&mut degs0, r, 0);
    }
    canonicalize(&mut labels0, m);
    layers[0].insert(Key { labels: labels0, degs: degs0, ecount: 0 }, (0, None));

    let total_v = (m * n) as u16;

    for c in 0..n {
        for r in 0..m {
            let last_col = c + 1 == n;
            let last_row = r + 1 == m;
            let p_index = c * m + r;

            // Drain the previous layer and fill the next.
            // We .iter() rather than .drain() because we need the previous layer
            // to remain queryable during backtracking later.
            let prev_keys: Vec<Key> = layers[p_index].keys().copied().collect();
            for k in prev_keys {
                let (preserved_so_far, _pred) = *layers[p_index].get(&k).unwrap();
                let labels = k.labels;
                let degs = k.degs;
                let ecount = k.ecount;

                let comp_r = get4(labels, r);
                let deg_r = get2(degs, r);
                let comp_down = if !last_row { get4(labels, r + 1) } else { 0 };

                let x_max = if last_col { 0 } else { 1 };
                let y_max = if last_row { 0 } else { 1 };
                for x in 0..=x_max {
                    for y in 0..=y_max {
                        if y == 1 && comp_r != 0 && comp_r == comp_down { continue; }
                        let deg_final = deg_r + x + y;
                        if deg_final == 0 && total_v > 1 { continue; }

                        let e2 = ecount + x as u16 + y as u16;
                        if e2 > total_v - 1 { continue; }

                        let mut labels_cur = labels;
                        let mut degs_cur = degs;
                        let mut need_fresh = false;

                        if y == 1 {
                            merge_labels(&mut labels_cur, m, comp_r, comp_down);
                            if !last_row {
                                let d = get2(degs_cur, r + 1);
                                set2(&mut degs_cur, r + 1, d + 1);
                            }
                        }

                        let mut labels_next = labels_cur;
                        let mut degs_next = degs_cur;

                        if last_col {
                            set4(&mut labels_next, r, 0);
                            set2(&mut degs_next, r, 0);
                        } else {
                            if x == 1 {
                                set4(&mut labels_next, r, get4(labels_cur, r));
                            } else {
                                set4(&mut labels_next, r, 15);
                                need_fresh = true;
                            }
                            set2(&mut degs_next, r, x);
                        }

                        if comp_r != 0 && !comp_present(labels_next, m, comp_r) && !(last_col && last_row) {
                            continue;
                        }

                        if !(x == 1 && y == 0 && !last_col) {
                            if need_fresh || !is_canonical(labels_next, m) {
                                canonicalize(&mut labels_next, m);
                            }
                        }

                        let add_pres = (deg_final == grid_deg(m, n, r, c)) as i32;
                        let val = preserved_so_far + add_pres;

                        let nk = Key { labels: labels_next, degs: degs_next, ecount: e2 };
                        let pred = Pred { prev_key: k, x: x as u8, y: y as u8 };
                        match layers[p_index + 1].get_mut(&nk) {
                            Some(slot) => {
                                if val > slot.0 {
                                    slot.0 = val;
                                    slot.1 = Some(pred);
                                }
                            }
                            None => {
                                layers[p_index + 1].insert(nk, (val, Some(pred)));
                            }
                        }
                    }
                }
            }
        }
    }

    // Find the best accept state in the final layer.
    let final_layer = &layers[pcount];
    let mut best: Option<(Key, i32)> = None;
    for (k, &(v, _)) in final_layer.iter() {
        if k.ecount == total_v - 1 && k.labels == 0 {
            if best.map_or(true, |(_, bv)| v > bv) {
                best = Some((*k, v));
            }
        }
    }
    let (mut cur_key, value) = best.expect("DP found no spanning tree (impossible for connected grid)");

    // Backward walk: reconstruct (x, y) decisions per cell, in reverse.
    let mut decisions: Vec<(u8, u8)> = Vec::with_capacity(pcount);
    for t in (1..=pcount).rev() {
        let (_, pred) = layers[t].get(&cur_key).expect("backtrack lost").clone();
        let pred = pred.expect("non-initial state must have predecessor");
        decisions.push((pred.x, pred.y));
        cur_key = pred.prev_key;
    }
    decisions.reverse();

    // Convert decisions back to edges. Decision i corresponds to cell (r, c) where
    // i = c*m + r. (x = horizontal edge to (r, c+1); y = vertical edge to (r+1, c).)
    let mut edges: Vec<Edge> = Vec::with_capacity(pcount);
    for (i, &(x, y)) in decisions.iter().enumerate() {
        let c = i / m;
        let r = i % m;
        if x == 1 {
            // horizontal edge (r, c) -- (r, c+1)
            edges.push(((r, c), (r, c + 1)));
        }
        if y == 1 {
            // vertical edge (r, c) -- (r+1, c)
            edges.push(((r, c), (r + 1, c)));
        }
    }

    Some(Witness { m, n, transposed, value, edges })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::solve;

    #[test]
    fn witness_value_matches_solve_small() {
        for m in 1..=6 {
            for n in 1..=6 {
                let v_solve = solve(m, n, None, false);
                let w = solve_with_witness(m, n).expect("non-empty grid");
                assert_eq!(v_solve, w.value, "value mismatch at m={m} n={n}");
            }
        }
    }

    #[test]
    fn witness_value_matches_solve_8x8() {
        // Heavier check on a few specific (m, n) pairs.
        for &(m, n) in &[(7, 7), (8, 8), (3, 15), (4, 12)] {
            let v_solve = solve(m, n, None, false);
            let w = solve_with_witness(m, n).expect("non-empty grid");
            assert_eq!(v_solve, w.value, "value mismatch at m={m} n={n}");
        }
    }

    #[test]
    fn witness_edges_form_spanning_tree() {
        for m_user in 2..=5 {
            for n_user in 2..=5 {
                let w = solve_with_witness(m_user, n_user).expect("non-empty grid");
                // Validate in the canonical frame (m_eff, n_eff) where m_eff ≤ n_eff.
                let (m_eff, n_eff) = (w.m, w.n);
                // edge count check
                assert_eq!(w.edges.len(), m_eff * n_eff - 1, "edge count m={m_user} n={n_user}");
                // all edges are valid grid edges in the canonical frame
                for &(a, b) in &w.edges {
                    let dr = (a.0 as isize - b.0 as isize).abs();
                    let dc = (a.1 as isize - b.1 as isize).abs();
                    assert_eq!(dr + dc, 1, "non-grid edge {a:?}--{b:?} in {m_user}x{n_user}");
                    assert!(a.0 < m_eff && b.0 < m_eff && a.1 < n_eff && b.1 < n_eff,
                            "OOB edge {a:?}--{b:?} in {m_user}x{n_user} (canonical {m_eff}x{n_eff})");
                }
                // connectedness via union-find
                let mut parent: Vec<usize> = (0..m_eff * n_eff).collect();
                fn find(parent: &mut Vec<usize>, mut x: usize) -> usize {
                    while parent[x] != x {
                        parent[x] = parent[parent[x]];
                        x = parent[x];
                    }
                    x
                }
                for &(a, b) in &w.edges {
                    let ai = a.0 * n_eff + a.1;
                    let bi = b.0 * n_eff + b.1;
                    let ra = find(&mut parent, ai);
                    let rb = find(&mut parent, bi);
                    assert_ne!(ra, rb, "cycle {a:?}--{b:?} in {m_user}x{n_user}");
                    parent[ra] = rb;
                }
                let root = find(&mut parent, 0);
                for v in 1..m_eff * n_eff {
                    let r = find(&mut parent, v);
                    assert_eq!(r, root, "disconnected at v={v} in {m_user}x{n_user}");
                }
                // full-degree count
                let mut deg = vec![0u8; m_eff * n_eff];
                for &(a, b) in &w.edges {
                    deg[a.0 * n_eff + a.1] += 1;
                    deg[b.0 * n_eff + b.1] += 1;
                }
                let mut full = 0i32;
                for r in 0..m_eff {
                    for c in 0..n_eff {
                        if deg[r * n_eff + c] == grid_deg(m_eff, n_eff, r, c) {
                            full += 1;
                        }
                    }
                }
                assert_eq!(full, w.value,
                           "full-degree mismatch in {m_user}x{n_user}: counted {full} expected {}",
                           w.value);
            }
        }
    }
}
