//! Phase 4 transfer-matrix machinery.
//!
//! Builds the column-to-column transition graph for the full-degree
//! spanning-tree problem on an `m x n` grid graph, then computes the
//! maximum-mean cycle (Karp's algorithm) to obtain the rational asymptotic
//! growth rate `α_m = lim P(m, n) / n` and an explicit optimal periodic
//! motif.
//!
//! State representation
//! --------------------
//!
//! A column state captures the "interface" exposed to the next column when
//! we have just finalized all internal-to-column-c choices and all
//! horizontal edges between columns c-1 and c. Per row r ∈ 0..m:
//!
//!   * `labels[r]` ∈ 1..k: canonical component id of vertex (r, c) inside
//!     the partial spanning forest constructed so far. Canonicalized so
//!     that ids appear in increasing order top-to-bottom (1 first, then 2
//!     the next time a fresh id is needed, etc.).
//!   * `pdeg[r]` ∈ 0..3: partial degree of (r, c). For an interior column
//!     this counts the left-neighbor edge plus any vertical edges within
//!     column c. The right-neighbor edge has not been decided yet.
//!
//! A transition (s -> s') chooses, for the next column c+1:
//!   * `h[0..m]` ∈ {0, 1}^m: horizontal edge between (r, c) and (r, c+1).
//!   * `v[0..m-1]` ∈ {0, 1}^{m-1}: vertical edge between (r, c+1) and
//!     (r+1, c+1).
//!
//! Validity constraints (interior regime, c ≥ 1 and c+1 ≤ n-2):
//!   * The 2m-vertex union-find seeded by the components of column c plus
//!     fresh singletons for column c+1 must remain a forest after applying
//!     the `h` and `v` unions (no cycle).
//!   * Every column-c component must "survive": at least one row r in
//!     that component has `h[r] = 1` (otherwise the component closes off
//!     as an isolated tree, leaving the full spanning tree disconnected).
//!
//! Gain
//! ----
//!
//! After the transition, every vertex in column c is finalized — its tree
//! degree equals `pdeg[r] + h[r]`. We treat both columns as interior, so
//! the target grid degree of (r, c) is 4 if 0 < r < m-1, else 3. The gain
//! is the number of rows where the final degree equals the target. Karp's
//! max-mean cycle on this weighted transition graph yields `α_m`.
//!
//! Boundary handling
//! -----------------
//!
//! The first and last columns of an `m x n` grid have one fewer neighbor
//! per row, so their gain accounting differs. The asymptotic slope `α_m`
//! is determined entirely by the interior cycle and is unaffected; the
//! exact closed-form value of `P(m, n)` requires analyzing the boundary
//! transient (Phase 4.5), which is handled separately.

use crate::transfer_util::Frac;
use std::collections::VecDeque;

/// Maximum supported width. The 4-bit-per-row label packing fits 16, but
/// we cap at 10 to keep state-space enumeration tractable in seconds.
pub const MAX_M_TRANSFER: usize = 10;

#[inline]
fn get4(x: u64, i: usize) -> u8 {
    ((x >> (i * 4)) & 0xF) as u8
}
#[inline]
fn set4(x: &mut u64, i: usize, v: u8) {
    let s = i * 4;
    *x = (*x & !(0xFu64 << s)) | ((v as u64) << s);
}
#[inline]
fn get2(x: u32, i: usize) -> u8 {
    ((x >> (i * 2)) & 0x3) as u8
}
#[inline]
fn set2(x: &mut u32, i: usize, v: u8) {
    let s = i * 2;
    *x = (*x & !(0x3u32 << s)) | ((v as u32) << s);
}

/// Canonical column state: per-row component label (4 bits) and partial
/// degree (2 bits). For m ≤ 16, both fit in u64 / u32.
#[derive(Clone, Copy, Eq, PartialEq, Hash, Debug)]
pub struct State {
    pub labels: u64,
    pub pdeg: u32,
}

/// Canonicalize labels so they appear as 1, 2, 3, ... in row order.
/// In-place. Assumes original labels in 1..15 (or 0 if absent — but absent
/// is invalid in interior-column contexts).
fn canonicalize(labels: &mut u64, m: usize) {
    let mut map = [0u8; 16];
    let mut next: u8 = 1;
    let mut new_labels: u64 = 0;
    for i in 0..m {
        let id = get4(*labels, i);
        if id == 0 {
            continue;
        }
        let nid = if map[id as usize] == 0 {
            let v = next;
            next += 1;
            map[id as usize] = v;
            v
        } else {
            map[id as usize]
        };
        set4(&mut new_labels, i, nid);
    }
    *labels = new_labels;
}

/// Target tree degree for vertex (r, c) when both c-1 and c+1 columns
/// exist (interior regime). 3 if r is on the top or bottom border, else 4.
#[inline]
fn interior_target_deg(r: usize, m: usize) -> u8 {
    if r == 0 || r + 1 == m {
        3
    } else {
        4
    }
}

/// Maximum partial degree (left + verticals) achievable for row r in an
/// interior column. Equals interior_target_deg(r, m) − 1 (right edge
/// excluded). Used to bound `pdeg` in the canonical state.
#[inline]
fn max_pdeg_interior(r: usize, m: usize) -> u8 {
    interior_target_deg(r, m) - 1
}

/// Tiny union-find on at most 2 * MAX_M_TRANSFER nodes.
#[derive(Clone)]
struct DSU {
    parent: [u8; 2 * MAX_M_TRANSFER + 2],
}

impl DSU {
    fn new(n: usize) -> Self {
        let mut s = DSU {
            parent: [0u8; 2 * MAX_M_TRANSFER + 2],
        };
        for i in 0..n {
            s.parent[i] = i as u8;
        }
        s
    }
    fn find(&mut self, mut x: u8) -> u8 {
        while self.parent[x as usize] != x {
            self.parent[x as usize] = self.parent[self.parent[x as usize] as usize];
            x = self.parent[x as usize];
        }
        x
    }
    /// Returns true iff a and b were already in the same set (cycle!).
    fn union_or_cycle(&mut self, a: u8, b: u8) -> bool {
        let ra = self.find(a);
        let rb = self.find(b);
        if ra == rb {
            return true;
        }
        self.parent[ra as usize] = rb;
        false
    }
}

/// Enumerate every canonical interior column state reachable as a
/// (col c) configuration when c is in the interior (i.e. with both
/// neighbors present). Strategy: forward BFS from a seed set of states
/// reachable as "column 1 after one full step from a column 0 boundary",
/// and saturate under the interior transition relation.
///
/// In practice we want every state that participates in any interior
/// transition cycle. Since reachable-from-some-valid-prefix is hard to
/// pin down without simulating boundary columns, we enumerate every
/// state that can appear as the right-side of any valid interior
/// transition. We do this by a fixed-point: start from any column-0-like
/// initial state (no left neighbor, so pdeg ≤ vertical contributions),
/// step forward, and add discovered states until closure.
///
/// Returns the deduped state list together with the transition adjacency
/// list (state index -> Vec<(dst_index, gain)>), restricted to the
/// reachable subset.
pub struct TransitionGraph {
    pub states: Vec<State>,
    /// Outgoing edges. edges[i] = Vec<(j, gain)> where transition i -> j
    /// has gain `gain` (the count of rows in column c that became
    /// full-degree as a result of the chosen transition).
    pub edges: Vec<Vec<(u32, i32)>>,
}

impl TransitionGraph {
    pub fn num_states(&self) -> usize {
        self.states.len()
    }
    pub fn num_edges(&self) -> usize {
        self.edges.iter().map(|e| e.len()).sum()
    }
}

/// Enumerate "column-0 boundary" states: column c=0 has no left neighbor,
/// so pdeg[r] for vertex (r,0) only counts vertical edges within column
/// 0. We pick a subset of m-1 vertical edges respecting the no-cycle
/// constraint; since column 0 alone is a path graph on m vertices, any
/// subset is acyclic. Each such subset induces components (connected
/// runs) and per-row pdeg ∈ {0,1,2}.
fn boundary_initial_states(m: usize) -> Vec<State> {
    if m == 0 {
        return vec![];
    }
    if m == 1 {
        // single vertex, label 1, pdeg 0
        let mut labels = 0u64;
        set4(&mut labels, 0, 1);
        return vec![State { labels, pdeg: 0 }];
    }
    let mut out = Vec::new();
    let v_count = m - 1;
    for mask in 0u32..(1u32 << v_count) {
        // Build labels: components are runs of consecutive rows joined by
        // present vertical edges.
        let mut labels = 0u64;
        let mut pdeg = 0u32;
        let mut cur_label: u8 = 1;
        set4(&mut labels, 0, cur_label);
        for r in 0..v_count {
            let v_present = (mask >> r) & 1 == 1;
            if v_present {
                // edge between r and r+1 — same component, increment pdeg
                let d = get2(pdeg, r);
                set2(&mut pdeg, r, d + 1);
                let d2 = get2(pdeg, r + 1);
                set2(&mut pdeg, r + 1, d2 + 1);
                set4(&mut labels, r + 1, cur_label);
            } else {
                cur_label += 1;
                set4(&mut labels, r + 1, cur_label);
            }
        }
        canonicalize(&mut labels, m);
        // Note: for column 0 boundary we want a subset of states where
        // pdeg[r] reflects ONLY internal verticals (no left edge), which
        // is exactly what we computed.
        out.push(State { labels, pdeg });
    }
    out
}

/// Apply a transition (h, v) from column-c state `s` to column-(c+1).
/// Returns Some((next_state, gain)) on success, None on validity failure.
///
/// `h_mask`: bit r set if horizontal edge (r,c)-(r,c+1) chosen.
/// `v_mask`: bit r (for r ∈ 0..m-1) set if vertical edge (r,c+1)-(r+1,c+1) chosen.
///
/// `interior_in`: whether column c is interior (i.e. c ≥ 1) — affects how
/// we assess the gain (the target degree for finalized vertex (r,c)).
/// `interior_out`: whether column c+1 is interior (i.e. c+1 ≤ n-2) —
/// affects allowable pdeg values for the produced state.
fn step(
    m: usize,
    s: &State,
    h_mask: u32,
    v_mask: u32,
    interior_in: bool,
    interior_out: bool,
) -> Option<(State, i32)> {
    // -- Build union-find over 2m nodes. Nodes 0..m are column c rows
    // -- (with their existing component classes from `s.labels`); nodes
    // -- m..2m are column c+1 rows (start as singletons).
    let n_nodes = 2 * m;
    let mut dsu = DSU::new(n_nodes);
    // Seed col-c equivalences from labels.
    let mut first_for_label = [u8::MAX; 16];
    for r in 0..m {
        let lab = get4(s.labels, r);
        if lab == 0 {
            continue;
        }
        if first_for_label[lab as usize] == u8::MAX {
            first_for_label[lab as usize] = r as u8;
        } else {
            // Already exists; merge with first representative.
            dsu.union_or_cycle(r as u8, first_for_label[lab as usize]);
        }
    }
    // -- Apply horizontal edges.
    let mut col_c_seen = [false; 16];
    for r in 0..m {
        if (h_mask >> r) & 1 == 1 {
            let lab = get4(s.labels, r);
            if lab > 0 {
                col_c_seen[lab as usize] = true;
            }
            // Union col-c row r (node r) with col-c+1 row r (node m+r).
            if dsu.union_or_cycle(r as u8, (m + r) as u8) {
                return None; // cycle
            }
        }
    }
    // -- Connectivity: every col-c label must have at least one h=1.
    for lab in 1..=15u8 {
        if first_for_label[lab as usize] != u8::MAX && !col_c_seen[lab as usize] {
            return None; // dead component
        }
    }
    // -- Apply vertical edges within column c+1.
    for r in 0..m.saturating_sub(1) {
        if (v_mask >> r) & 1 == 1 {
            if dsu.union_or_cycle((m + r) as u8, (m + r + 1) as u8) {
                return None; // cycle
            }
        }
    }

    // -- Compute next pdeg for column c+1.
    let mut next_pdeg: u32 = 0;
    for r in 0..m {
        let mut d: u8 = 0;
        if (h_mask >> r) & 1 == 1 {
            d += 1;
        }
        if r > 0 && (v_mask >> (r - 1)) & 1 == 1 {
            d += 1;
        }
        if r + 1 < m && (v_mask >> r) & 1 == 1 {
            d += 1;
        }
        // Bound check: d cannot exceed the per-row maximum partial degree
        // for the next column.
        let cap = if interior_out {
            max_pdeg_interior(r, m)
        } else {
            // For final column (no right neighbor), pdeg can saturate the
            // grid degree. interior_target_deg already excludes the right
            // edge, so the cap is the same. We still allow it; final-column
            // handling is for boundary mode only.
            max_pdeg_interior(r, m)
        };
        if d > cap {
            return None;
        }
        set2(&mut next_pdeg, r, d);
    }

    // -- Build next labels: each row r in col c+1 gets a component id
    // -- determined by the dsu root of node (m+r). We re-canonicalize.
    let mut raw_labels = 0u64;
    for r in 0..m {
        let root = dsu.find((m + r) as u8);
        // Map roots to small ids 1..15 in row order.
        // We'll do a temp mapping from root id to a small id.
        set4(&mut raw_labels, r, root + 1); // +1 since canonicalize treats 0 as "absent"
    }
    canonicalize(&mut raw_labels, m);

    // -- Compute gain: how many col-c rows have final degree (pdeg + h)
    // -- matching the target.
    let mut gain: i32 = 0;
    for r in 0..m {
        let d_final = get2(s.pdeg, r) + ((h_mask >> r) & 1) as u8;
        let target = if interior_in {
            interior_target_deg(r, m)
        } else {
            // Column 0: top/bottom row target = 2 (right + down or right + up),
            // interior row target = 3 (right + up + down). I.e. one less
            // than interior. We won't use this branch for cycle analysis;
            // just keep symmetric for completeness.
            interior_target_deg(r, m) - 1
        };
        if d_final == target {
            gain += 1;
        }
    }

    Some((
        State {
            labels: raw_labels,
            pdeg: next_pdeg,
        },
        gain,
    ))
}

/// Enumerate every transition out of state `s` in the interior regime.
/// Each is (next_state, gain).
pub fn outgoing_interior(m: usize, s: &State) -> Vec<(State, i32)> {
    let mut out = Vec::new();
    let h_count = 1u32 << m;
    let v_count = if m == 0 { 1 } else { 1u32 << (m - 1) };
    for h in 0..h_count {
        for v in 0..v_count {
            if let Some((s2, g)) = step(m, s, h, v, true, true) {
                out.push((s2, g));
            }
        }
    }
    out
}

/// Build the full interior transition graph for width m, by forward BFS
/// from boundary-initial states until closure under interior transitions.
///
/// We accept that the BFS visits every reachable interior state from any
/// starting column-0 configuration. For the max-mean cycle, only the
/// states inside any strongly-connected component matter.
pub fn build_interior_graph(m: usize) -> TransitionGraph {
    use hashbrown::HashMap;
    assert!(m >= 1 && m <= MAX_M_TRANSFER);

    // Step 1: seed BFS from column-0 states (which produce column-1
    // states via one boundary->interior transition). The column-1 states
    // are the starting point of interior transitions.
    let init_states = boundary_initial_states(m);
    let mut state_index: HashMap<State, u32> = HashMap::new();
    let mut states: Vec<State> = Vec::new();
    let mut queue: VecDeque<u32> = VecDeque::new();

    // First, do one (boundary -> interior) step from each init state to
    // populate column-1 candidates. Actually for the purposes of finding
    // every interior cycle, we can simply seed with EVERY column-1 state
    // produced by every (h, v) transition out of every column-0 state.
    for s0 in &init_states {
        // Step from "col 0 boundary" to "col 1 interior".
        let h_count = 1u32 << m;
        let v_count = if m == 0 { 1 } else { 1u32 << (m - 1) };
        for h in 0..h_count {
            for v in 0..v_count {
                if let Some((s1, _)) = step(m, s0, h, v, false, true) {
                    if !state_index.contains_key(&s1) {
                        let idx = states.len() as u32;
                        state_index.insert(s1, idx);
                        states.push(s1);
                        queue.push_back(idx);
                    }
                }
            }
        }
    }

    // Step 2: BFS-saturate by interior-interior transitions.
    // Deduplicate parallel edges, keeping max gain (only the best matters
    // for max-mean cycle).
    let mut edges: Vec<Vec<(u32, i32)>> = Vec::new();
    while let Some(idx) = queue.pop_front() {
        while (edges.len() as u32) <= idx {
            edges.push(Vec::new());
        }
        let s = states[idx as usize];
        let outs = outgoing_interior(m, &s);
        // Group outs by destination state, keep max gain per dst.
        let mut best_to: hashbrown::HashMap<u32, i32> = hashbrown::HashMap::new();
        for (s2, gain) in outs {
            let j = match state_index.get(&s2) {
                Some(&j) => j,
                None => {
                    let j = states.len() as u32;
                    state_index.insert(s2, j);
                    states.push(s2);
                    queue.push_back(j);
                    j
                }
            };
            best_to
                .entry(j)
                .and_modify(|cur| {
                    if gain > *cur {
                        *cur = gain;
                    }
                })
                .or_insert(gain);
        }
        edges[idx as usize] = best_to.into_iter().map(|(j, g)| (j, g)).collect();
    }
    while edges.len() < states.len() {
        edges.push(Vec::new());
    }

    TransitionGraph { states, edges }
}

/// Tarjan's strongly-connected-components.
fn tarjan_sccs(num_v: usize, adj: &[Vec<(u32, i32)>]) -> Vec<Vec<u32>> {
    let mut index: Vec<i32> = vec![-1; num_v];
    let mut low: Vec<i32> = vec![0; num_v];
    let mut on_stack: Vec<bool> = vec![false; num_v];
    let mut stack: Vec<u32> = Vec::new();
    let mut idx_counter: i32 = 0;
    let mut sccs: Vec<Vec<u32>> = Vec::new();

    // Iterative Tarjan to avoid stack overflow on large graphs.
    enum Frame {
        Enter(u32),
        Resume(u32, usize),
    }
    for start in 0..num_v as u32 {
        if index[start as usize] >= 0 {
            continue;
        }
        let mut work: Vec<Frame> = vec![Frame::Enter(start)];
        while let Some(frame) = work.pop() {
            match frame {
                Frame::Enter(v) => {
                    index[v as usize] = idx_counter;
                    low[v as usize] = idx_counter;
                    idx_counter += 1;
                    stack.push(v);
                    on_stack[v as usize] = true;
                    work.push(Frame::Resume(v, 0));
                }
                Frame::Resume(v, mut i) => {
                    let nbrs = &adj[v as usize];
                    let mut recurse = None;
                    while i < nbrs.len() {
                        let w = nbrs[i].0;
                        if index[w as usize] < 0 {
                            // recurse
                            work.push(Frame::Resume(v, i + 1));
                            recurse = Some(w);
                            break;
                        } else if on_stack[w as usize] {
                            if index[w as usize] < low[v as usize] {
                                low[v as usize] = index[w as usize];
                            }
                        }
                        i += 1;
                    }
                    if let Some(w) = recurse {
                        work.push(Frame::Enter(w));
                        continue;
                    }
                    // done; first compute low based on children
                    // (children's low values were updated when they returned;
                    // but our iterative scheme requires post-order: when a
                    // child completes, we need to bubble its low up to v.
                    // Since we don't have explicit return, do it now by
                    // re-scanning children with index >= index[v] that
                    // were visited after v.
                    let v_index = index[v as usize];
                    for &(w, _) in &adj[v as usize] {
                        if index[w as usize] > v_index {
                            // child of v in DFS tree; bubble low[w]
                            if low[w as usize] < low[v as usize] {
                                low[v as usize] = low[w as usize];
                            }
                        }
                    }
                    if low[v as usize] == index[v as usize] {
                        let mut comp = Vec::new();
                        loop {
                            let w = stack.pop().unwrap();
                            on_stack[w as usize] = false;
                            comp.push(w);
                            if w == v {
                                break;
                            }
                        }
                        sccs.push(comp);
                    }
                }
            }
        }
    }
    sccs
}

/// Memory-efficient Karp's max-mean-cycle algorithm.
///
/// Standard Karp stores `F[k][v]` for all k=0..n and all v in the SCC,
/// requiring O(n²) memory. Here we use a two-pass streaming variant:
///
///   Pass 1: compute `F[n][v]` for all v, keeping only the current and
///           previous "row" of F (O(n) memory).
///   Pass 2: re-run the same DP but at each step k > 0, after computing
///           F[k][v], evaluate per-vertex
///                f(k, v) = (F[n][v] - F[k][v]) / (n - k)
///           and update `min_over_k[v]`. Then α = max_v min_over_k[v].
///
/// Memory: O(|V_S|) — independent of n. Time: O(|V_S| · |E_S|).
///
/// Returns Some((num, den, cycle_vertex_seq)) describing the maximum
/// mean cycle, or None if the SCC has no edges.
pub fn karp_max_mean_cycle_streaming(
    verts: &[u32],
    adj: &[Vec<(u32, i32)>],
) -> Option<(i64, i64, Vec<u32>)> {
    let n = verts.len();
    if n == 0 {
        return None;
    }
    let max_global = *verts.iter().max().unwrap() as usize;
    let mut local: Vec<i32> = vec![-1; max_global + 1];
    for (i, &v) in verts.iter().enumerate() {
        local[v as usize] = i as i32;
    }

    // Build local adjacency (filter to within-SCC edges).
    let mut ladj: Vec<Vec<(u32, i32)>> = vec![Vec::new(); n];
    let mut has_edge = false;
    for (i, &v) in verts.iter().enumerate() {
        for &(w, gw) in &adj[v as usize] {
            let lw = local.get(w as usize).copied().unwrap_or(-1);
            if lw >= 0 {
                ladj[i].push((lw as u32, gw));
                has_edge = true;
            }
        }
    }
    if !has_edge {
        return None;
    }

    const NEG_INF: i64 = i64::MIN / 4;

    // Pass 1: compute F[n][v]. Source = vertex 0.
    let mut f_prev: Vec<i64> = vec![NEG_INF; n];
    f_prev[0] = 0;
    let mut f_n: Vec<i64> = f_prev.clone();
    for _k in 0..n {
        let mut f_cur: Vec<i64> = vec![NEG_INF; n];
        for u in 0..n {
            if f_prev[u] == NEG_INF {
                continue;
            }
            for &(v, w) in &ladj[u] {
                let cand = f_prev[u] + w as i64;
                if cand > f_cur[v as usize] {
                    f_cur[v as usize] = cand;
                }
            }
        }
        f_n = f_cur.clone();
        f_prev = f_cur;
    }

    // Pass 2: compute running min over k of (F[n][v] - F[k][v]) / (n - k),
    // per vertex. Track the best (k, v) achieving overall max.
    f_prev = vec![NEG_INF; n];
    f_prev[0] = 0;
    // For each v, maintain min over k ≤ current_k of (num, den) =
    // (F[n][v] - F[k][v], n - k). We compare via cross-multiplication.
    let mut min_num_per_v: Vec<i64> = vec![i64::MAX; n];
    let mut min_den_per_v: Vec<i64> = vec![1; n];
    let mut min_k_per_v: Vec<i32> = vec![-1; n];
    for v in 0..n {
        if f_n[v] == NEG_INF {
            continue;
        }
        // k = 0
        let num = f_n[v] - f_prev[v];
        let den = n as i64;
        if min_k_per_v[v] < 0 {
            min_num_per_v[v] = num;
            min_den_per_v[v] = den;
            min_k_per_v[v] = 0;
        }
    }
    for k in 1..=n {
        let mut f_cur: Vec<i64> = vec![NEG_INF; n];
        for u in 0..n {
            if f_prev[u] == NEG_INF {
                continue;
            }
            for &(v, w) in &ladj[u] {
                let cand = f_prev[u] + w as i64;
                if cand > f_cur[v as usize] {
                    f_cur[v as usize] = cand;
                }
            }
        }
        if k < n {
            for v in 0..n {
                if f_n[v] == NEG_INF || f_cur[v] == NEG_INF {
                    continue;
                }
                let num = f_n[v] - f_cur[v];
                let den = (n - k) as i64;
                let better = if min_k_per_v[v] < 0 {
                    true
                } else {
                    num * min_den_per_v[v] < min_num_per_v[v] * den
                };
                if better {
                    min_num_per_v[v] = num;
                    min_den_per_v[v] = den;
                    min_k_per_v[v] = k as i32;
                }
            }
        }
        f_prev = f_cur;
    }

    // Best v: max of min_per_v.
    let mut best_v: i32 = -1;
    let mut best_num: i64 = 0;
    let mut best_den: i64 = 1;
    for v in 0..n {
        if min_k_per_v[v] < 0 {
            continue;
        }
        let better = if best_v < 0 {
            true
        } else {
            min_num_per_v[v] * best_den > best_num * min_den_per_v[v]
        };
        if better {
            best_v = v as i32;
            best_num = min_num_per_v[v];
            best_den = min_den_per_v[v];
        }
    }
    if best_v < 0 {
        return None;
    }

    // To recover the cycle, do a third pass that records predecessors at
    // every step. Memory cost: O(n · |V|) just for predecessors —
    // unavoidable for cycle extraction. For very large graphs this can be
    // skipped (return cycle = empty) and only the rational mean returned.
    // We do the pred-table reconstruction here but cap memory at ~2GB by
    // emitting a synthetic cycle if the table would be too large.
    let pred_bytes = (n + 1)
        .checked_mul(n)
        .and_then(|x| x.checked_mul(8))
        .unwrap_or(usize::MAX);
    if pred_bytes > 2_000_000_000 {
        // Skip cycle reconstruction; return the rational mean and an empty
        // representative-cycle list. The caller knows the value is correct.
        let g = gcd(best_num.unsigned_abs() as i64, best_den);
        let g = if g == 0 { 1 } else { g };
        return Some((best_num / g, best_den / g, Vec::new()));
    }

    // Re-run with pred recording (concise version, similar to original
    // Karp). For efficiency we only record predecessors for each k, not
    // all F values.
    let mut pred_table: Vec<Vec<i32>> = vec![vec![-1; n]; n + 1];
    let mut f_prev2: Vec<i64> = vec![NEG_INF; n];
    f_prev2[0] = 0;
    for k in 0..n {
        let mut f_cur: Vec<i64> = vec![NEG_INF; n];
        for u in 0..n {
            if f_prev2[u] == NEG_INF {
                continue;
            }
            for &(v, w) in &ladj[u] {
                let cand = f_prev2[u] + w as i64;
                if cand > f_cur[v as usize] {
                    f_cur[v as usize] = cand;
                    pred_table[k + 1][v as usize] = u as i32;
                }
            }
        }
        f_prev2 = f_cur;
    }

    // Walk back n steps from best_v.
    let mut path: Vec<i32> = Vec::with_capacity(n + 1);
    let mut cur = best_v;
    let mut k = n;
    path.push(cur);
    while k > 0 {
        let p = pred_table[k][cur as usize];
        if p < 0 {
            break;
        }
        path.push(p);
        cur = p;
        k -= 1;
    }
    // Find a repeated vertex in `path` to isolate a cycle.
    let mut first_seen: hashbrown::HashMap<i32, usize> = hashbrown::HashMap::new();
    let mut cycle_local: Vec<i32> = Vec::new();
    for (pos, &node) in path.iter().enumerate() {
        if let Some(&old) = first_seen.get(&node) {
            cycle_local = path[old..=pos].to_vec();
            break;
        }
        first_seen.insert(node, pos);
    }
    if cycle_local.is_empty() {
        let g = gcd(best_num.unsigned_abs() as i64, best_den);
        let g = if g == 0 { 1 } else { g };
        return Some((best_num / g, best_den / g, Vec::new()));
    }
    cycle_local.reverse();
    let cycle_global: Vec<u32> = cycle_local.iter().map(|&l| verts[l as usize]).collect();
    let cycle_global =
        if cycle_global.len() >= 2 && cycle_global[0] == *cycle_global.last().unwrap() {
            cycle_global[..cycle_global.len() - 1].to_vec()
        } else {
            cycle_global
        };

    // Recompute true cycle weight to reduce to lowest terms.
    let cyc_n = cycle_global.len();
    let mut wsum: i64 = 0;
    for i in 0..cyc_n {
        let a = cycle_global[i];
        let b = cycle_global[(i + 1) % cyc_n];
        let mut found: Option<i64> = None;
        for &(w, gw) in &adj[a as usize] {
            if w == b {
                let gi = gw as i64;
                if found.map_or(true, |x| gi > x) {
                    found = Some(gi);
                }
            }
        }
        wsum += found.unwrap_or(0);
    }
    let cyc_den = cyc_n as i64;
    let g = gcd(wsum.unsigned_abs() as i64, cyc_den);
    let g = if g == 0 { 1 } else { g };
    Some((wsum / g, cyc_den / g, cycle_global))
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

    /// Karp on the transfer-matrix gives the closed-form alpha_m from
    /// recurrences.md for the widths where the state space is small
    /// enough (m ≤ 6).
    #[test]
    fn karp_matches_recurrence_alpha_for_small_m() {
        // (m, expected alpha numerator, expected alpha denominator)
        let cases = [(3, 4i64, 3i64), (4, 2, 1), (5, 2, 1), (6, 5, 2)];
        for &(m, en, ed) in &cases {
            let (alpha, _cyc, _g) = compute_alpha(m);
            assert_eq!(
                alpha,
                Frac::new(en, ed),
                "Karp alpha_m mismatch at m={m}: got {} expected {}/{}",
                alpha,
                en,
                ed
            );
        }
    }
}

/// Compute α_m and an optimal interior cycle. Returns (α_m as Frac,
/// optimal cycle as state indices, full transition graph for further
/// inspection).
pub fn compute_alpha(m: usize) -> (Frac, Vec<u32>, TransitionGraph) {
    let t0 = std::time::Instant::now();
    let g = build_interior_graph(m);
    let t_build = t0.elapsed().as_secs_f64();
    let n = g.states.len();
    let n_edges: usize = g.edges.iter().map(|e| e.len()).sum();
    eprintln!(
        "[transfer] m={} graph built: {} states, {} edges in {:.2}s",
        m, n, n_edges, t_build
    );
    let t1 = std::time::Instant::now();
    let sccs = tarjan_sccs(n, &g.edges);
    eprintln!(
        "[transfer] m={} SCCs: {} (largest {}) in {:.2}s",
        m,
        sccs.len(),
        sccs.iter().map(|s| s.len()).max().unwrap_or(0),
        t1.elapsed().as_secs_f64()
    );
    // Karp on each SCC; take maximum.
    let mut best: Option<(i64, i64, Vec<u32>)> = None;
    for comp in &sccs {
        if comp.len() < 2 {
            // Singleton SCC: only matters if it has a self-loop with a
            // weight that beats current best.
            let v = comp[0];
            let mut best_self: Option<i32> = None;
            for &(w, gain) in &g.edges[v as usize] {
                if w == v {
                    best_self = Some(match best_self {
                        Some(b) => b.max(gain),
                        None => gain,
                    });
                }
            }
            if let Some(g_self) = best_self {
                let cand_num = g_self as i64;
                let cand_den = 1i64;
                best = match best {
                    None => Some((cand_num, cand_den, vec![v])),
                    Some((bn, bd, bc)) => {
                        if cand_num * bd > bn * cand_den {
                            Some((cand_num, cand_den, vec![v]))
                        } else {
                            Some((bn, bd, bc))
                        }
                    }
                };
            }
            continue;
        }
        let t_scc = std::time::Instant::now();
        if let Some((num, den, cyc)) = karp_max_mean_cycle_streaming(comp, &g.edges) {
            eprintln!(
                "[transfer] Karp(streaming) on SCC of {} states: {}/{} ({:.2}s)",
                comp.len(),
                num,
                den,
                t_scc.elapsed().as_secs_f64()
            );
            best = match best {
                None => Some((num, den, cyc)),
                Some((bn, bd, bc)) => {
                    if num * bd > bn * den {
                        Some((num, den, cyc))
                    } else {
                        Some((bn, bd, bc))
                    }
                }
            };
        }
    }
    match best {
        Some((num, den, cyc)) => (Frac::new(num, den), cyc, g),
        None => (Frac::new(0, 1), Vec::new(), g),
    }
}
