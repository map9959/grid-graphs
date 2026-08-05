use hashbrown::HashMap;
use rayon::prelude::*;
use std::hash::{BuildHasherDefault, Hash, Hasher};
use std::sync::{Arc, Mutex};
use std::{cmp::max, env};

const MAX_M: usize = 16; // width cap (can go up to 16 due to 4-bit labels & 2-bit deg packing)
                         // Packed frontier:
                         // labels: 4 bits per row in u64  (rows 0..9 -> 40 bits)
                         // degs:   2 bits per row in u32  (rows 0..9 -> 20 bits)

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

// Compact key representing frontier state. We implement a faster hasher below
// exploiting that the structure is already POD with limited entropy.
#[derive(Clone, Copy, Eq, PartialEq)]
struct Key {
    labels: u64, // 4-bit ids per row; 0 means empty slot (canonicalized sequentially)
    degs: u32,   // 2-bit degree so far per row-vertex in frontier
    ecount: u16, // edges chosen so far
}

#[derive(Clone, Copy, Eq, PartialEq)]
struct FullKey {
    labels: u64,
    full: u16,
}

impl std::hash::Hash for FullKey {
    #[inline(always)]
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u64(self.labels);
        state.write_u16(self.full);
    }
}

impl std::hash::Hash for Key {
    #[inline(always)]
    fn hash<H: Hasher>(&self, state: &mut H) {
        // Mix like a 16-byte packet. Compose into 128 bits with padding.
        // Layout (little endian): labels (64) | degs (32) | next_id (8) | ecount (16) | pad (8)
        state.write_u64(self.labels);
        let tail = (self.degs as u64) | ((self.ecount as u64) << 32);
        state.write_u64(tail);
    }
}

// Extremely small, fast hasher (fxhash is already good, but this avoids per-entry
// pointer chasing for BuildHasher). Fowler–Noll or a simple reversible mix.
#[derive(Default)]
struct KHasher(u64);
impl Hasher for KHasher {
    #[inline(always)]
    fn write(&mut self, bytes: &[u8]) {
        // fallback (rare)
        let mut h = self.0;
        for &b in bytes {
            h = h.rotate_left(5) ^ (b as u64).wrapping_mul(0x517cc1b727220a95);
        }
        self.0 = h;
    }
    #[inline(always)]
    fn write_u64(&mut self, i: u64) {
        // Single-round reversible mix
        let mut x = i ^ 0x9e3779b97f4a7c15;
        x = (x ^ (x >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
        x = (x ^ (x >> 27)).wrapping_mul(0x94d049bb133111eb);
        self.0 ^= x;
    }
    #[inline(always)]
    fn finish(&self) -> u64 {
        self.0
    }
}
type FastBuild = BuildHasherDefault<KHasher>;

#[inline]
fn key_shard(k: &Key, mask: usize) -> usize {
    let mut h = KHasher::default();
    k.hash(&mut h);
    (h.finish() as usize) & mask
}

fn shrink_to_cap(map: &mut HashMap<Key, i32, FastBuild>, cap: usize) {
    if cap == 0 || map.len() <= cap {
        return;
    }
    let mut items: Vec<(Key, i32)> = map.drain().collect();
    items.select_nth_unstable_by(cap, |a, b| b.1.cmp(&a.1));
    items.truncate(cap);
    map.reserve(cap);
    map.extend(items);
}

mod analysis; // bring in bounds
use analysis::{lower_bound, lower_bound_band, upper_bound, upper_bound_relaxed};
mod motif;
mod plotly_vis; // interactive HTML plotting
mod transfer; // Phase 4 transfer-matrix + Karp's max-mean cycle
mod transfer_util;
mod witness; // Phase 4 motif extraction from optimal witness

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
    for i in 0..m {
        if get4(labels, i) == comp {
            return true;
        }
    }
    false
}

#[inline]
fn merge_labels(labels: &mut u64, m: usize, a: u8, b: u8) {
    if a == 0 || b == 0 || a == b {
        return;
    }
    for i in 0..m {
        if get4(*labels, i) == b {
            set4(labels, i, a);
        }
    }
}

#[inline]
fn canonicalize(labels: &mut u64, m: usize) {
    // Map first-seen nonzero ids to 1..k in order of appearance.
    let mut map = [0u8; 16]; // component ids limited to 4 bits
    let mut next: u8 = 1;
    let mut new_labels: u64 = 0;
    for i in 0..m {
        let id = get4(*labels, i);
        if id == 0 {
            continue;
        }
        let slot = map[id as usize];
        let nid = if slot == 0 {
            let v = next;
            next += 1;
            map[id as usize] = v;
            v
        } else {
            slot
        };
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
        if id == 0 {
            continue;
        }
        bit |= 1u32 << id;
        if id > max_id {
            max_id = id;
        }
    }
    if max_id == 0 {
        return true;
    }
    // bits 1..=max_id must all be set; bit 0 ignored.
    let needed = ((1u32 << (max_id + 1)) - 2) & !1; // set bits 1..max_id
    (bit & needed) == needed && bit.count_ones() as u8 == max_id
}

#[inline(never)]
fn solve(m: usize, n: usize, beam_cap: Option<usize>, prune: bool) -> i32 {
    solve_inner(m, n, beam_cap, prune, false)
}

#[inline(never)]
fn solve_profile(m: usize, n: usize, beam_cap: Option<usize>, prune: bool) -> i32 {
    solve_inner(m, n, beam_cap, prune, true)
}

fn canonicalize_full(labels: &mut u64, m: usize) {
    canonicalize(labels, m);
}

fn first_unused_label(labels: u64, m: usize) -> u8 {
    let mut used = [false; 16];
    for i in 0..m {
        used[get4(labels, i) as usize] = true;
    }
    (1u8..=15)
        .find(|&id| !used[id as usize])
        .expect("frontier width leaves a free 4-bit label")
}

fn fullkey_shard(k: &FullKey, mask: usize) -> usize {
    let mut h = KHasher::default();
    k.hash(&mut h);
    (h.finish() as usize) & mask
}

fn fullub_step(
    m: usize,
    n: usize,
    r: usize,
    c: usize,
    k: FullKey,
    cur_full_bool: bool,
) -> Option<FullKey> {
    let left_label = if c > 0 { get4(k.labels, r) } else { 0 };
    let left_full = c > 0 && ((k.full >> r) & 1 == 1);
    let up_label = if r > 0 { get4(k.labels, r - 1) } else { 0 };
    let up_full = r > 0 && ((k.full >> (r - 1)) & 1 == 1);
    let force_left = c > 0 && (left_full || cur_full_bool);
    let force_up = r > 0 && (up_full || cur_full_bool);
    let keep_current = r + 1 < m || c + 1 < n;
    let mut labels_next = k.labels;
    let mut full_next = k.full;
    set4(&mut labels_next, r, 0);
    full_next &= !(1u16 << r);

    let current_label = match (force_left, force_up) {
        (true, true) => {
            if left_label == up_label {
                return None;
            }
            merge_labels(&mut labels_next, m, left_label, up_label);
            left_label
        }
        (true, false) => left_label,
        (false, true) => up_label,
        (false, false) => first_unused_label(labels_next, m),
    };

    if keep_current {
        set4(&mut labels_next, r, current_label);
        if cur_full_bool {
            full_next |= 1u16 << r;
        } else {
            full_next &= !(1u16 << r);
        }
    }

    for i in 0..m {
        let id = get4(labels_next, i);
        if id == 0 {
            full_next &= !(1u16 << i);
        }
    }
    canonicalize_full(&mut labels_next, m);
    Some(FullKey {
        labels: labels_next,
        full: full_next,
    })
}

#[inline(never)]
fn fullub(mut m: usize, mut n: usize) -> i32 {
    if m == 0 || n == 0 {
        return 0;
    }
    if m > n {
        std::mem::swap(&mut m, &mut n);
    }
    assert!(
        m <= 15,
        "fullub uses 4-bit component labels and supports width <= 15"
    );

    let mut state: HashMap<FullKey, i32, FastBuild> = HashMap::with_hasher(FastBuild::default());
    state.insert(FullKey { labels: 0, full: 0 }, 0);
    const FULLUB_PAR_THRESHOLD: usize = 8192;

    for c in 0..n {
        for r in 0..m {
            let old_state =
                std::mem::replace(&mut state, HashMap::with_hasher(FastBuild::default()));
            if old_state.len() < FULLUB_PAR_THRESHOLD {
                let mut next: HashMap<FullKey, i32, FastBuild> =
                    HashMap::with_hasher(FastBuild::default());
                next.reserve(old_state.len().saturating_mul(2));
                for (k, val) in old_state {
                    for cur_full_bool in [false, true] {
                        let Some(nk) = fullub_step(m, n, r, c, k, cur_full_bool) else {
                            continue;
                        };
                        let nv = val + cur_full_bool as i32;
                        next.entry(nk)
                            .and_modify(|prev| {
                                if nv > *prev {
                                    *prev = nv;
                                }
                            })
                            .or_insert(nv);
                    }
                }
                state = next;
            } else {
                let old_vec: Vec<(FullKey, i32)> = old_state.into_iter().collect();
                let n_threads = rayon::current_num_threads().max(1);
                let shard_count = (n_threads * 16).next_power_of_two().max(64);
                let shard_mask = shard_count - 1;
                let per_shard_reserve = old_vec
                    .len()
                    .saturating_mul(2)
                    .checked_div(shard_count)
                    .unwrap_or(0)
                    .saturating_add(1);
                let shards: Arc<Vec<Mutex<HashMap<FullKey, i32, FastBuild>>>> = Arc::new(
                    (0..shard_count)
                        .map(|_| {
                            let mut shard = HashMap::with_hasher(FastBuild::default());
                            shard.reserve(per_shard_reserve);
                            Mutex::new(shard)
                        })
                        .collect(),
                );
                old_vec
                    .par_chunks((old_vec.len() / (n_threads * 4)).max(8192))
                    .for_each(|chunk| {
                        let mut local: HashMap<FullKey, i32, FastBuild> =
                            HashMap::with_hasher(FastBuild::default());
                        local.reserve(chunk.len().saturating_mul(2));
                        for &(k, val) in chunk {
                            for cur_full_bool in [false, true] {
                                let Some(nk) = fullub_step(m, n, r, c, k, cur_full_bool) else {
                                    continue;
                                };
                                let nv = val + cur_full_bool as i32;
                                local
                                    .entry(nk)
                                    .and_modify(|prev| {
                                        if nv > *prev {
                                            *prev = nv;
                                        }
                                    })
                                    .or_insert(nv);
                            }
                        }
                        for (k, v) in local {
                            let idx = fullkey_shard(&k, shard_mask);
                            let mut shard = shards[idx].lock().unwrap();
                            shard
                                .entry(k)
                                .and_modify(|prev| {
                                    if v > *prev {
                                        *prev = v;
                                    }
                                })
                                .or_insert(v);
                        }
                    });
                let shards = match Arc::try_unwrap(shards) {
                    Ok(shards) => shards,
                    Err(_) => unreachable!("fullub workers completed"),
                };
                let mut next: HashMap<FullKey, i32, FastBuild> =
                    HashMap::with_hasher(FastBuild::default());
                let total_len: usize = shards.iter().map(|s| s.lock().unwrap().len()).sum();
                next.reserve(total_len);
                for shard in shards {
                    next.extend(shard.into_inner().unwrap());
                }
                state = next;
            }
        }
    }

    state.into_values().max().unwrap_or(0)
}

#[derive(Clone, Copy, Default)]
struct FullSet {
    bits: [u64; 4],
}

impl FullSet {
    fn set(&mut self, idx: usize, value: bool) {
        let word = idx / 64;
        let bit = idx % 64;
        if value {
            self.bits[word] |= 1u64 << bit;
        } else {
            self.bits[word] &= !(1u64 << bit);
        }
    }

    fn get(&self, idx: usize) -> bool {
        ((self.bits[idx / 64] >> (idx % 64)) & 1) == 1
    }
}

fn fullub_with_witness(mut m: usize, mut n: usize) -> (i32, Vec<bool>) {
    if m == 0 || n == 0 {
        return (0, Vec::new());
    }
    let (orig_m, orig_n) = (m, n);
    let transposed = m > n;
    if transposed {
        std::mem::swap(&mut m, &mut n);
    }
    assert!(
        m <= 15,
        "fullub uses 4-bit component labels and supports width <= 15"
    );

    let mut state: HashMap<FullKey, (i32, FullSet), FastBuild> =
        HashMap::with_hasher(FastBuild::default());
    state.insert(FullKey { labels: 0, full: 0 }, (0, FullSet::default()));
    const FULLUB_PAR_THRESHOLD: usize = 8192;

    for c in 0..n {
        for r in 0..m {
            let p = c * m + r;
            let old_state =
                std::mem::replace(&mut state, HashMap::with_hasher(FastBuild::default()));
            if old_state.len() < FULLUB_PAR_THRESHOLD {
                let mut next: HashMap<FullKey, (i32, FullSet), FastBuild> =
                    HashMap::with_hasher(FastBuild::default());
                next.reserve(old_state.len().saturating_mul(2));
                for (k, (val, chosen)) in old_state {
                    for cur_full in [false, true] {
                        let Some(nk) = fullub_step(m, n, r, c, k, cur_full) else {
                            continue;
                        };
                        let nv = val + cur_full as i32;
                        let mut nchosen = chosen;
                        nchosen.set(p, cur_full);
                        match next.get_mut(&nk) {
                            Some(slot) => {
                                if nv > slot.0 {
                                    *slot = (nv, nchosen);
                                }
                            }
                            None => {
                                next.insert(nk, (nv, nchosen));
                            }
                        }
                    }
                }
                state = next;
            } else {
                let old_vec: Vec<(FullKey, (i32, FullSet))> = old_state.into_iter().collect();
                let n_threads = rayon::current_num_threads().max(1);
                let shard_count = (n_threads * 16).next_power_of_two().max(64);
                let shard_mask = shard_count - 1;
                let per_shard_reserve = old_vec
                    .len()
                    .saturating_mul(2)
                    .checked_div(shard_count)
                    .unwrap_or(0)
                    .saturating_add(1);
                let shards: Arc<Vec<Mutex<HashMap<FullKey, (i32, FullSet), FastBuild>>>> = Arc::new(
                    (0..shard_count)
                        .map(|_| {
                            let mut shard = HashMap::with_hasher(FastBuild::default());
                            shard.reserve(per_shard_reserve);
                            Mutex::new(shard)
                        })
                        .collect(),
                );
                old_vec
                    .par_chunks((old_vec.len() / (n_threads * 4)).max(8192))
                    .for_each(|chunk| {
                        let mut local: HashMap<FullKey, (i32, FullSet), FastBuild> =
                            HashMap::with_hasher(FastBuild::default());
                        local.reserve(chunk.len().saturating_mul(2));
                        for &(k, (val, chosen)) in chunk {
                            for cur_full in [false, true] {
                                let Some(nk) = fullub_step(m, n, r, c, k, cur_full) else {
                                    continue;
                                };
                                let nv = val + cur_full as i32;
                                let mut nchosen = chosen;
                                nchosen.set(p, cur_full);
                                match local.get_mut(&nk) {
                                    Some(slot) => {
                                        if nv > slot.0 {
                                            *slot = (nv, nchosen);
                                        }
                                    }
                                    None => {
                                        local.insert(nk, (nv, nchosen));
                                    }
                                }
                            }
                        }
                        for (k, v) in local {
                            let idx = fullkey_shard(&k, shard_mask);
                            let mut shard = shards[idx].lock().unwrap();
                            match shard.get_mut(&k) {
                                Some(slot) => {
                                    if v.0 > slot.0 {
                                        *slot = v;
                                    }
                                }
                                None => {
                                    shard.insert(k, v);
                                }
                            }
                        }
                    });
                let shards = match Arc::try_unwrap(shards) {
                    Ok(shards) => shards,
                    Err(_) => unreachable!("fullub witness workers completed"),
                };
                let mut next: HashMap<FullKey, (i32, FullSet), FastBuild> =
                    HashMap::with_hasher(FastBuild::default());
                let total_len: usize = shards.iter().map(|s| s.lock().unwrap().len()).sum();
                next.reserve(total_len);
                for shard in shards {
                    next.extend(shard.into_inner().unwrap());
                }
                state = next;
            }
        }
    }

    let (best, chosen) = state.into_values().max_by_key(|(v, _)| *v).unwrap();
    let mut user_full = vec![false; orig_m * orig_n];
    for c in 0..n {
        for r in 0..m {
            let src = c * m + r;
            let (ur, uc) = if transposed { (c, r) } else { (r, c) };
            user_full[ur * orig_n + uc] = chosen.get(src);
        }
    }
    (best, user_full)
}

fn complete_forced_tree(
    m: usize,
    n: usize,
    full: &[bool],
) -> Option<Vec<((usize, usize), (usize, usize))>> {
    let total = m * n;
    if full.len() != total || total == 0 {
        return None;
    }
    let mut parent: Vec<usize> = (0..total).collect();
    fn find(parent: &mut [usize], mut x: usize) -> usize {
        while parent[x] != x {
            parent[x] = parent[parent[x]];
            x = parent[x];
        }
        x
    }

    let mut edges = Vec::new();
    let mut optional = Vec::new();
    for r in 0..m {
        for c in 0..n {
            let a = r * n + c;
            if c + 1 < n {
                let b = r * n + c + 1;
                let e = ((r, c), (r, c + 1));
                if full[a] || full[b] {
                    let ra = find(&mut parent, a);
                    let rb = find(&mut parent, b);
                    if ra == rb {
                        return None;
                    }
                    parent[ra] = rb;
                    edges.push(e);
                } else {
                    optional.push((a, b, e));
                }
            }
            if r + 1 < m {
                let b = (r + 1) * n + c;
                let e = ((r, c), (r + 1, c));
                if full[a] || full[b] {
                    let ra = find(&mut parent, a);
                    let rb = find(&mut parent, b);
                    if ra == rb {
                        return None;
                    }
                    parent[ra] = rb;
                    edges.push(e);
                } else {
                    optional.push((a, b, e));
                }
            }
        }
    }

    for (a, b, e) in optional {
        let ra = find(&mut parent, a);
        let rb = find(&mut parent, b);
        if ra != rb {
            parent[ra] = rb;
            edges.push(e);
        }
    }
    if edges.len() != total - 1 {
        return None;
    }
    let root = find(&mut parent, 0);
    for v in 1..total {
        if find(&mut parent, v) != root {
            return None;
        }
    }
    Some(edges)
}

fn count_full_from_edges(m: usize, n: usize, edges: &[((usize, usize), (usize, usize))]) -> i32 {
    let mut deg = vec![0u8; m * n];
    for &((r1, c1), (r2, c2)) in edges {
        deg[r1 * n + c1] += 1;
        deg[r2 * n + c2] += 1;
    }
    let mut count = 0;
    for r in 0..m {
        for c in 0..n {
            if deg[r * n + c] == grid_deg(m, n, r, c) {
                count += 1;
            }
        }
    }
    count
}

#[inline(never)]
fn solve_inner(
    mut m: usize,
    mut n: usize,
    beam_cap: Option<usize>,
    prune: bool,
    profile: bool,
) -> i32 {
    if m == 0 || n == 0 {
        return 0;
    }
    if m == 1 && n == 1 {
        return 1;
    }

    // transpose so width is smaller
    if m > n {
        std::mem::swap(&mut m, &mut n);
    }
    assert!(m <= MAX_M);

    // precompute grid degrees: rows = m (≤ MAX_M), cols = n (variable, can exceed MAX_M).
    // Use a flat Vec<u8> indexed via gdeg[r*n + c].
    let mut gdeg: Vec<u8> = vec![0u8; m * n];
    for r in 0..m {
        for c in 0..n {
            gdeg[r * n + c] = grid_deg(m, n, r, c);
        }
    }
    // Helper closure for legibility.
    let gd = |r: usize, c: usize| -> u8 { gdeg[r * n + c] };

    // Flatten degrees in processing (c-major, r-minor) order for fast suffix bounds.
    let pcount = m * n; // total cells
    let mut deg_list: Vec<u8> = Vec::with_capacity(pcount);
    for c in 0..n {
        for r in 0..m {
            deg_list.push(gd(r, c));
        }
    }
    let mut prefix_deg_sum: Vec<i32> = vec![0; pcount + 1];
    for p in 0..pcount {
        prefix_deg_sum[p + 1] = prefix_deg_sum[p] + deg_list[p] as i32;
    }
    // Suffix counts of degrees 1..4 (ignore index 0). suffix_counts[p] = counts AFTER processing cell p-1 (so use p+1 after processing p).
    let mut suffix_counts: Vec<[u16; 5]> = vec![[0u16; 5]; pcount + 1];
    for p in (0..pcount).rev() {
        suffix_counts[p] = suffix_counts[p + 1];
        let d = deg_list[p] as usize;
        if d <= 4 {
            suffix_counts[p][d] += 1;
        }
    }

    // initial frontier: column 0 before any row processed
    let mut labels0: u64 = 0;
    let mut degs0: u32 = 0;
    for r in 0..m {
        set4(&mut labels0, r, (r as u8) + 1);
        set2(&mut degs0, r, 0);
    }
    let mut state: HashMap<Key, i32, FastBuild> = HashMap::with_hasher(FastBuild::default());
    state.reserve(1 << 14);
    canonicalize(&mut labels0, m); // trivial but keeps invariant
    state.insert(
        Key {
            labels: labels0,
            degs: degs0,
            ecount: 0,
        },
        0,
    );

    let total_v = (m * n) as u16;
    let total_deficiency = (2 * (m - 1) * (n - 1)) as i32;

    // simple admissible upper bound on future edges usable without cycles:
    // at (r,c) the remaining potential edges is
    // rem_right = m * (n-1 - c), rem_down = (m-1 - r) + (m-1)*(n-1 - c)
    let mut rem_edges_upper = vec![vec![0u16; n]; m];
    for c in 0..n {
        for r in 0..m {
            let rem_right = (n - 1 - c) as u16 * m as u16;
            let rem_down_here_col = (m - 1 - r) as u16;
            let rem_down_cols = (m - 1) as u16 * (n - 1 - c) as u16;
            rem_edges_upper[r][c] = rem_right + rem_down_here_col + rem_down_cols;
        }
    }

    // Remaining vertices after processing (r,c) (simple bound kept for reference / fallback)
    let mut rem_vertices = vec![vec![0u16; n]; m];
    for c2 in 0..n {
        for r2 in 0..m {
            rem_vertices[r2][c2] = (m - (r2 + 1)) as u16 + (m * (n - (c2 + 1))) as u16;
        }
    }

    let low_mem = env::var("LOWMEM")
        .map(|s| s == "1" || s.eq_ignore_ascii_case("true"))
        .unwrap_or(false);
    let target_floor = env::var("TARGET")
        .ok()
        .and_then(|s| s.parse::<i32>().ok())
        .filter(|&v| v >= 0);

    let mut profile_log: Vec<(usize, usize, usize, f64, usize)> = Vec::new();
    // (col, row, state_count_in, time_secs, prune_skips)
    let mut total_prune_skips: usize = 0;

    // Threshold above which we use parallel expansion. For tiny states the
    // overhead of thread spawning + merge dominates.
    const PAR_THRESHOLD: usize = 8192;

    for c in 0..n {
        for r in 0..m {
            let layer_start = if profile {
                Some(std::time::Instant::now())
            } else {
                None
            };
            let state_in = state.len();
            let last_col = c + 1 == n;
            let last_row = r + 1 == m;

            // Linear position index for (r,c) in processing order
            let p_index = c * m + r;

            // Pre-fetch values referenced in the hot inner closure.
            let counts = suffix_counts[p_index + 1];
            let rem_up = rem_edges_upper[r][c];
            let rem_v = rem_vertices[r][c] as i32;
            let prefix_deg_after = prefix_deg_sum[p_index + 1];

            let safe_future_potential = |nk: &Key, e2: u16, rem_edges_needed: u16| -> i32 {
                let mut possible_counts = [0i32; 5];
                for d in 1..=4 {
                    possible_counts[d] = counts[d] as i32;
                }

                // For frontier vertices, some incident edges have already
                // been decided. If any such edge is absent, that vertex can no
                // longer become full-degree. If it is still possible, its
                // already-selected partial degree can be credited toward the
                // final degree-incidence budget.
                let mut partial_credit = 0i32;
                let mut partial_all = 0i32;
                let mut forced_capacity = 0i32;
                for i in 0..m {
                    partial_all += get2(nk.degs, i) as i32;
                    let (vr, vc, processed_incidents) = if i <= r {
                        if last_col {
                            continue;
                        }
                        // Slot i now represents (i, c+1); only its left edge
                        // has been decided so far.
                        (i, c + 1, 1i32)
                    } else {
                        // Slot i still represents (i, c). Its left edge was
                        // decided in the previous column, and for i=r+1 the up
                        // edge was just decided by this cell's y choice.
                        let left = if c > 0 { 1 } else { 0 };
                        let up = if i == r + 1 { 1 } else { 0 };
                        (i, c, left + up)
                    };
                    let partial = get2(nk.degs, i) as i32;
                    let grid_d = gd(vr, vc) as usize;
                    if partial < processed_incidents {
                        possible_counts[grid_d] -= 1;
                        forced_capacity += grid_d as i32 - 1;
                    } else {
                        partial_credit += partial;
                    }
                }

                let mut budget = 2 * rem_edges_needed as i32 + partial_credit;
                let mut potential = 0i32;
                for d in 1..=4 {
                    let avail = possible_counts[d].max(0);
                    if avail == 0 {
                        continue;
                    }
                    let fit = budget / d as i32;
                    if fit <= 0 {
                        break;
                    }
                    let take = avail.min(fit);
                    potential += take;
                    budget -= take * d as i32;
                    if budget <= 0 {
                        break;
                    }
                }

                // Deficiency packing bound for the unfinalized suffix. The
                // finalized prefix has tree-degree sum 2*e2 - partial_all; the
                // remaining deficiency must be absorbed by future non-full
                // vertices, each with capacity at most grid_degree - 1.
                let finalized_tree_deg = 2 * e2 as i32 - partial_all;
                let def_so_far = prefix_deg_after - finalized_tree_deg;
                let mut def_need = total_deficiency - def_so_far - forced_capacity;
                let mut extra_nonfull = 0i32;
                if def_need > 0 {
                    for d in (1..=4).rev() {
                        let cap = d as i32 - 1;
                        if cap <= 0 {
                            continue;
                        }
                        let avail = possible_counts[d].max(0);
                        if avail == 0 {
                            continue;
                        }
                        let need_here = (def_need + cap - 1) / cap;
                        let take = avail.min(need_here);
                        extra_nonfull += take;
                        def_need -= take * cap;
                        if def_need <= 0 {
                            break;
                        }
                    }
                }
                let possible_total: i32 = possible_counts.iter().map(|&x| x.max(0)).sum();
                let deficiency_potential = if def_need > 0 {
                    0
                } else {
                    possible_total.saturating_sub(extra_nonfull)
                };

                potential.min(deficiency_potential)
            };

            let expand = |k: Key,
                          preserved_so_far: i32,
                          local: &mut HashMap<Key, i32, FastBuild>,
                          local_best: &mut i32,
                          local_skips: &mut usize| {
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
                        if y == 1 && comp_r != 0 && comp_r == comp_down {
                            continue;
                        }
                        let deg_final = deg_r + x + y;
                        if deg_final == 0 && total_v > 1 {
                            continue;
                        }

                        let e2 = ecount + x as u16 + y as u16;
                        if e2 > total_v - 1 || e2 + rem_up < total_v - 1 {
                            continue;
                        }

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

                        if comp_r != 0
                            && !comp_present(labels_next, m, comp_r)
                            && !(last_col && last_row)
                        {
                            continue;
                        }

                        if !(x == 1 && y == 0 && !last_col) {
                            if need_fresh || !is_canonical(labels_next, m) {
                                canonicalize(&mut labels_next, m);
                            }
                        }

                        let add_pres = (deg_final == gd(r, c)) as i32;
                        let val = preserved_so_far + add_pres;

                        let nk = Key {
                            labels: labels_next,
                            degs: degs_next,
                            ecount: e2,
                        };
                        let rem_edges_needed = (total_v - 1) - e2;
                        if let Some(target) = target_floor {
                            // Safe feasibility pruning: even if every remaining
                            // vertex became full-degree, this branch cannot
                            // reach TARGET.
                            if val + rem_v < target {
                                *local_skips += 1;
                                continue;
                            }
                            let potential = safe_future_potential(&nk, e2, rem_edges_needed);
                            if val + potential < target {
                                *local_skips += 1;
                                continue;
                            }
                        }

                        if prune {
                            let mut budget = (2 * rem_edges_needed as u32) as i32;
                            let mut potential = 0i32;
                            for d in 1..=4 {
                                let mut avail = counts[d] as i32;
                                if avail == 0 {
                                    continue;
                                }
                                let fit = budget / d as i32;
                                if fit <= 0 {
                                    break;
                                }
                                if avail > fit {
                                    avail = fit;
                                }
                                potential += avail;
                                budget -= avail * d as i32;
                                if budget <= 0 {
                                    break;
                                }
                            }
                            if val + potential < *local_best {
                                *local_skips += 1;
                                continue;
                            }
                        }
                        if let Some(prev) = local.get_mut(&nk) {
                            if val > *prev {
                                *prev = val;
                                if val > *local_best {
                                    *local_best = val;
                                }
                            }
                        } else {
                            local.insert(nk, val);
                            if val > *local_best {
                                *local_best = val;
                            }
                        }
                    }
                }
            };

            let use_parallel = !low_mem && state_in >= PAR_THRESHOLD;
            let (next_state, prune_skips_layer) = if !use_parallel {
                let old_state =
                    std::mem::replace(&mut state, HashMap::with_hasher(FastBuild::default()));
                // Sequential/low-memory path: stream directly from the current
                // layer instead of materializing state_vec and per-thread maps.
                let mut local: HashMap<Key, i32, FastBuild> =
                    HashMap::with_hasher(FastBuild::default());
                local.reserve(state_in.saturating_mul(2));
                let mut local_best: i32 = -1;
                let mut local_skips: usize = 0;
                for (k, v) in old_state.into_iter() {
                    expand(k, v, &mut local, &mut local_best, &mut local_skips);
                }
                (local, local_skips)
            } else {
                let old_state =
                    std::mem::replace(&mut state, HashMap::with_hasher(FastBuild::default()));
                // Collect state into a Vec for parallel iteration. This is
                // faster on large layers but has a higher peak-memory footprint;
                // set LOWMEM=1 to force the streaming path above.
                let state_vec: Vec<(Key, i32)> = old_state.into_iter().collect();
                // Parallel path: chunk the state, expand each chunk to a
                // thread-local hashmap with its own running best, then merge
                // that chunk into global shards before the worker returns.
                // This keeps parallelism but avoids holding all local maps and
                // a separate full-size merged map at peak memory.
                let n_threads = rayon::current_num_threads().max(1);
                let default_chunk_size = (state_vec.len() + n_threads - 1) / n_threads;
                let chunk_size = if let Some(cap) = beam_cap {
                    default_chunk_size.min((cap / (n_threads * 8)).max(8192))
                } else {
                    default_chunk_size
                };
                let chunks: Vec<&[(Key, i32)]> = state_vec.chunks(chunk_size).collect();

                let shard_count = (n_threads * 16).next_power_of_two().max(64);
                let shard_mask = shard_count - 1;
                let per_shard_reserve = state_vec
                    .len()
                    .saturating_mul(2)
                    .checked_div(shard_count)
                    .unwrap_or(0)
                    .saturating_add(1);
                let shards: Arc<Vec<Mutex<HashMap<Key, i32, FastBuild>>>> = Arc::new(
                    (0..shard_count)
                        .map(|_| {
                            let mut shard = HashMap::with_hasher(FastBuild::default());
                            shard.reserve(per_shard_reserve);
                            Mutex::new(shard)
                        })
                        .collect(),
                );
                let local_beam_cap = beam_cap.map(|cap| (cap / (n_threads * 2)).max(8192));
                let shard_beam_cap =
                    beam_cap.map(|cap| (cap / shard_count).saturating_mul(2).max(4096));

                let total_skips: usize = chunks
                    .into_par_iter()
                    .map(|chunk| {
                        let mut local: HashMap<Key, i32, FastBuild> =
                            HashMap::with_hasher(FastBuild::default());
                        local.reserve(chunk.len().saturating_mul(2));
                        let mut local_best: i32 = -1;
                        let mut local_skips: usize = 0;
                        for &(k, v) in chunk {
                            expand(k, v, &mut local, &mut local_best, &mut local_skips);
                        }
                        if let Some(cap) = local_beam_cap {
                            shrink_to_cap(&mut local, cap);
                        }
                        let mut touched = Vec::new();
                        let mut seen = vec![false; shard_count];
                        for (k, v) in local.into_iter() {
                            let shard_idx = key_shard(&k, shard_mask);
                            if !seen[shard_idx] {
                                seen[shard_idx] = true;
                                touched.push(shard_idx);
                            }
                            let mut shard = shards[shard_idx].lock().unwrap();
                            shard
                                .entry(k)
                                .and_modify(|prev| {
                                    if v > *prev {
                                        *prev = v;
                                    }
                                })
                                .or_insert(v);
                        }
                        if let Some(cap) = shard_beam_cap {
                            for shard_idx in touched {
                                let mut shard = shards[shard_idx].lock().unwrap();
                                if shard.len() > cap.saturating_mul(2) {
                                    shrink_to_cap(&mut shard, cap);
                                }
                            }
                        }
                        local_skips
                    })
                    .sum();

                let shards = match Arc::try_unwrap(shards) {
                    Ok(shards) => shards,
                    Err(_) => unreachable!("all shard workers completed"),
                };
                let mut merged: HashMap<Key, i32, FastBuild> =
                    HashMap::with_hasher(FastBuild::default());
                let total_len: usize = shards.iter().map(|s| s.lock().unwrap().len()).sum();
                merged.reserve(total_len);
                for shard in shards.into_iter() {
                    let shard = shard.into_inner().unwrap();
                    merged.extend(shard.into_iter());
                }
                (merged, total_skips)
            };

            // optional beam pruning
            if let Some(cap) = beam_cap {
                if next_state.len() > cap {
                    let mut items: Vec<(Key, i32)> = next_state.into_iter().collect();
                    items.select_nth_unstable_by(cap, |a, b| b.1.cmp(&a.1));
                    items.truncate(cap);
                    let mut shrunk: HashMap<Key, i32, FastBuild> =
                        HashMap::with_capacity_and_hasher(cap, FastBuild::default());
                    for (k, v) in items {
                        shrunk.insert(k, v);
                    }
                    state = shrunk;
                } else {
                    state = next_state;
                }
            } else {
                state = next_state;
            }

            if profile {
                let dt = layer_start.unwrap().elapsed().as_secs_f64();
                total_prune_skips += prune_skips_layer;
                profile_log.push((c, r, state_in, dt, prune_skips_layer));
                if r + 1 == m {
                    eprintln!(
                        "[profile:live] col={:3} row={:3} state_in={:>10} layer_time={:>7.2}s prune_skips={:>10}",
                        c, r, state_in, dt, prune_skips_layer
                    );
                }
            }
        }
    }

    if profile {
        eprintln!(
            "[profile] m={} n={} total prune-skips={}",
            m, n, total_prune_skips
        );
        eprintln!("[profile] col row state_in    time    prune_skips");
        let mut col_totals: std::collections::BTreeMap<usize, (f64, usize, usize)> =
            std::collections::BTreeMap::new();
        for &(c, r, sin, dt, ps) in &profile_log {
            let entry = col_totals.entry(c).or_insert((0.0, 0, 0));
            entry.0 += dt;
            entry.1 = entry.1.max(sin);
            entry.2 += ps;
            // Print only the row=m-1 entry for compactness.
            if r + 1 == m {
                eprintln!(
                    "[profile] {:3} {:3} {:>10} {:>7.2}s {:>10}",
                    c, r, sin, dt, ps
                );
            }
        }
        eprintln!("[profile] === per-column ===");
        eprintln!("[profile] col  total_time  max_states  prune_skips");
        for (c, (dt, mx, ps)) in col_totals {
            eprintln!("[profile] {:3}  {:>9.2}s  {:>10}  {:>10}", c, dt, mx, ps);
        }
    }

    // accept only empty frontier and exactly V-1 edges
    let mut ans = -1i32;
    for (k, val) in state.into_iter() {
        if k.ecount == total_v - 1 && k.labels == 0 {
            ans = max(ans, val);
        }
    }
    ans
}

fn main() {
    // Usage:
    //   cargo run --release -- 10 10
    //   cargo run --release -- table 10 10
    // Optional: BEAM=<cap> for pruning, e.g., BEAM=600000
    let args: Vec<String> = env::args().collect();
    let beam_cap = match env::var("BEAM").ok().and_then(|s| s.parse::<usize>().ok()) {
        Some(v) if v > 0 => Some(v),
        _ => None,
    };
    let prune = env::var("PRUNE")
        .map(|s| s == "1" || s.eq_ignore_ascii_case("true"))
        .unwrap_or(false);

    if args.len() == 3 && args[1] == "alpha" {
        let m = args[2].parse::<usize>().expect("m");
        let (alpha, cycle, graph) = transfer::compute_alpha(m);
        println!(
            "# m={} states={} edges={} alpha={}",
            m,
            graph.num_states(),
            graph.num_edges(),
            alpha
        );
        println!("alpha_{}_decimal = {:.10}", m, alpha.as_f64());
        println!("optimal_cycle_length = {}", cycle.len());
        for (i, &idx) in cycle.iter().enumerate() {
            let s = graph.states[idx as usize];
            println!(
                "  step {} state_idx={} labels=0x{:x} pdeg=0x{:x}",
                i, idx, s.labels, s.pdeg
            );
        }
        return;
    }
    if args.len() == 3 && args[1] == "fullub" {
        let m = args[2].parse::<usize>().expect("m");
        let n = m;
        println!("{}", fullub(m, n));
        return;
    }
    if args.len() == 4 && args[1] == "fullub-witness" {
        let m = args[2].parse::<usize>().expect("m");
        let n = args[3].parse::<usize>().expect("n");
        let (value, full) = fullub_with_witness(m, n);
        println!("# fullub m={m} n={n} value={value}");
        for r in 0..m {
            for c in 0..n {
                print!("{}", if full[r * n + c] { 'X' } else { '.' });
            }
            println!();
        }
        match complete_forced_tree(m, n, &full) {
            Some(edges) => {
                let actual = count_full_from_edges(m, n, &edges);
                println!("# completion succeeded edges={} full={actual}", edges.len());
                for &((r1, c1), (r2, c2)) in &edges {
                    println!("{} {} {} {}", r1, c1, r2, c2);
                }
            }
            None => println!("# completion failed"),
        }
        return;
    }
    if args.len() == 4 && args[1] == "fullub-pattern" {
        let m = args[2].parse::<usize>().expect("m");
        let n = args[3].parse::<usize>().expect("n");
        let (value, full) = fullub_with_witness(m, n);
        let u_count = full.iter().filter(|&&x| !x).count();
        println!("# fullub m={m} n={n} value={value} nonfull={u_count}");
        println!("# F/full pattern (X=full, .=non-full):");
        for r in 0..m {
            for c in 0..n {
                print!("{}", if full[r * n + c] { 'X' } else { '.' });
            }
            println!();
        }
        println!("# U/non-full pattern (U=non-full, .=full):");
        for r in 0..m {
            for c in 0..n {
                print!("{}", if full[r * n + c] { '.' } else { 'U' });
            }
            println!();
        }
        if let Some(edges) = complete_forced_tree(m, n, &full) {
            let actual = count_full_from_edges(m, n, &edges);
            println!("# completion succeeded edges={} full={actual}", edges.len());
        } else {
            println!("# completion failed");
        }
        return;
    }
    if args.len() == 4 && args[1] == "fullub" {
        let m = args[2].parse::<usize>().expect("m");
        let n = args[3].parse::<usize>().expect("n");
        println!("{}", fullub(m, n));
        return;
    }
    if args.len() == 3 {
        let m = args[1].parse::<usize>().expect("m");
        let n = args[2].parse::<usize>().expect("n");
        let ans = if env::var("PROFILE").map(|s| s == "1").unwrap_or(false) {
            solve_profile(m, n, beam_cap, prune)
        } else {
            solve(m, n, beam_cap, prune)
        };
        if let Some(target) = env::var("TARGET").ok().and_then(|s| s.parse::<i32>().ok()) {
            if ans >= target {
                eprintln!("# TARGET={target} reached; reported value is at least the target");
            } else {
                eprintln!(
                    "# TARGET={target} not reached; target pruning may discard lower-valued optima"
                );
            }
        }
        println!("{}", ans);
        return;
    }
    if args.len() == 4 && args[1] == "table" {
        let mmax = args[2].parse::<usize>().expect("mmax");
        let nmax = args[3].parse::<usize>().expect("nmax");
        for m in 1..=mmax {
            let mut first = true;
            for n in 1..=nmax {
                let v = solve(m, n, beam_cap, prune);
                if !first {
                    print!(", ");
                } else {
                    first = false;
                }
                print!("{}", v);
            }
            println!();
        }
        return;
    }
    if args.len() == 4 && args[1] == "compare" {
        let mmax = args[2].parse::<usize>().expect("mmax");
        let nmax = args[3].parse::<usize>().expect("nmax");
        let csv = env::var("CSV")
            .map(|s| s == "1" || s.eq_ignore_ascii_case("true"))
            .unwrap_or(false);
        if csv {
            println!("m,n,actual,LB_simple,LB_band,UB_cap,UB_rel,gapU_cap,gapU_rel,gapL_band,act_dens,UBcap_dens,UBrel_dens,LBband_dens");
        } else {
            println!("# m n act LB_s LB_b UB_cap UB_rel gapUc gapUr gapLb act  UBc  UBr  LBb");
        }
        for m in 1..=mmax {
            for n in 1..=nmax {
                let act = solve(m, n, beam_cap, prune);
                let lb_s = lower_bound(m, n) as i32;
                let lb_b = lower_bound_band(m, n) as i32;
                let ub_cap = upper_bound(m, n) as i32;
                let ub_rel = upper_bound_relaxed(m, n) as i32;
                let gap_uc = ub_cap - act;
                let gap_ur = ub_rel - act;
                let gap_lb = act - lb_b;
                let area = (m * n) as f64;
                let dens = act as f64 / area;
                let dens_uc = ub_cap as f64 / area;
                let dens_ur = ub_rel as f64 / area;
                let dens_lb = lb_b as f64 / area;
                if csv {
                    println!("{m},{n},{act},{lb_s},{lb_b},{ub_cap},{ub_rel},{gap_uc},{gap_ur},{gap_lb},{dens:.6},{dens_uc:.6},{dens_ur:.6},{dens_lb:.6}");
                } else {
                    println!("{m:>2} {n:>2} {act:>4} {lb_s:>4} {lb_b:>4} {ub_cap:>6} {ub_rel:>6} {gap_uc:>5} {gap_ur:>5} {gap_lb:>5} {dens:>5.3} {dens_uc:>5.3} {dens_ur:>5.3} {dens_lb:>5.3}");
                }
            }
        }
        return;
    }
    if args.len() == 4 && args[1] == "bounds" {
        let m = args[2].parse::<usize>().expect("m");
        let n = args[3].parse::<usize>().expect("n");
        let lb_s = lower_bound(m, n);
        let lb_b = lower_bound_band(m, n);
        let ub_cap = upper_bound(m, n);
        let ub_rel = upper_bound_relaxed(m, n);
        println!("m,n,LB_simple,LB_band,UB_cap,UB_rel");
        println!("{m},{n},{lb_s},{lb_b},{ub_cap},{ub_rel}");
        return;
    }
    if args.len() == 4 && args[1] == "plotly" {
        let csv_path = std::path::Path::new(&args[2]);
        let out_dir = std::path::Path::new(&args[3]);
        match plotly_vis::write_heatmaps(csv_path, out_dir) {
            Ok(_) => eprintln!("Plotly HTML written to {:?}", out_dir),
            Err(e) => {
                eprintln!("Plotly generation failed: {e}");
                std::process::exit(1);
            }
        }
        return;
    }
    if args.len() == 4 && args[1] == "motif" {
        let m = args[2].parse::<usize>().expect("m");
        let n = args[3].parse::<usize>().expect("n");
        print!("{}", motif::analyze(m, n));
        return;
    }
    if args.len() == 4 && args[1] == "witness" {
        let m = args[2].parse::<usize>().expect("m");
        let n = args[3].parse::<usize>().expect("n");
        match witness::solve_with_witness(m, n) {
            Some(w) => {
                println!(
                    "# m={} n={} value={} transposed={} edges={}",
                    w.m,
                    w.n,
                    w.value,
                    w.transposed,
                    w.edges.len()
                );
                for &((r1, c1), (r2, c2)) in &w.edges {
                    println!("{} {} {} {}", r1, c1, r2, c2);
                }
            }
            None => {
                println!("# empty grid (m={} n={})", m, n);
            }
        }
        return;
    }
    eprintln!("Usage:");
    eprintln!("  {} m n", args[0]);
    eprintln!("  {} table M N", args[0]);
    eprintln!("  {} compare M N   # empirical vs bounds", args[0]);
    eprintln!(
        "  {} bounds M N    # formula bounds only, no DP solve",
        args[0]
    );
    eprintln!(
        "  {} plotly results.csv out_dir  # generate interactive HTML plots",
        args[0]
    );
    eprintln!(
        "  {} witness M N   # print one optimal spanning tree (edges)",
        args[0]
    );
    eprintln!(
        "  {} alpha M      # Phase 4: max-mean cycle on transfer graph (m <= 6)",
        args[0]
    );
    eprintln!(
        "  {} fullub M N   # forced-edge acyclicity upper bound",
        args[0]
    );
    eprintln!(
        "  {} fullub-witness M N  # print fullub set and completion tree",
        args[0]
    );
    eprintln!(
        "  {} fullub-pattern M N  # print full/non-full patterns only",
        args[0]
    );
    eprintln!(
        "  {} motif M N    # Phase 4: visualize optimal witness and detect period",
        args[0]
    );
    eprintln!("Env: BEAM=<cap>  # optional beam size",);
    eprintln!("     PRUNE=1      # enable heuristic pruning");
    eprintln!("     LOWMEM=1     # disable parallel expansion and stream layers");
    eprintln!("     TARGET=<val> # feasibility pruning for proving/reaching a value");
    eprintln!("     CSV=1        # CSV output for compare mode");
}

#[cfg(test)]
mod fullub_tests {
    use super::*;

    fn brute_fullub(m: usize, n: usize) -> i32 {
        let total = m * n;
        assert!(total <= 20);
        let mut best = 0i32;
        for mask in 0u64..(1u64 << total) {
            let mut parent: Vec<usize> = (0..total).collect();
            fn find(parent: &mut [usize], mut x: usize) -> usize {
                while parent[x] != x {
                    parent[x] = parent[parent[x]];
                    x = parent[x];
                }
                x
            }
            let selected = |idx: usize| ((mask >> idx) & 1) == 1;
            let mut cycle = false;
            for r in 0..m {
                for c in 0..n {
                    let a = r * n + c;
                    if c + 1 < n {
                        let b = r * n + c + 1;
                        if selected(a) || selected(b) {
                            let ra = find(&mut parent, a);
                            let rb = find(&mut parent, b);
                            if ra == rb {
                                cycle = true;
                                break;
                            }
                            parent[ra] = rb;
                        }
                    }
                    if r + 1 < m {
                        let b = (r + 1) * n + c;
                        if selected(a) || selected(b) {
                            let ra = find(&mut parent, a);
                            let rb = find(&mut parent, b);
                            if ra == rb {
                                cycle = true;
                                break;
                            }
                            parent[ra] = rb;
                        }
                    }
                }
                if cycle {
                    break;
                }
            }
            if !cycle {
                best = best.max(mask.count_ones() as i32);
            }
        }
        best
    }

    #[test]
    fn fullub_matches_bruteforce_small() {
        for m in 1..=4 {
            for n in 1..=4 {
                assert_eq!(fullub(m, n), brute_fullub(m, n), "{m}x{n}");
            }
        }
    }

    #[test]
    fn exact_solution_below_fullub_small() {
        for m in 1..=6 {
            for n in 1..=8 {
                assert!(solve(m, n, None, false) <= fullub(m, n), "{m}x{n}");
            }
        }
    }

    #[test]
    fn fullub_witness_matches_value_small() {
        for m in 1..=5 {
            for n in 1..=5 {
                let (value, full) = fullub_with_witness(m, n);
                assert_eq!(value, fullub(m, n), "{m}x{n}");
                assert_eq!(value, full.iter().filter(|&&x| x).count() as i32, "{m}x{n}");
            }
        }
    }
}
