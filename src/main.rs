use hashbrown::HashMap;
use std::{cmp::max, env};
use std::hash::{BuildHasherDefault, Hasher};

const MAX_M: usize = 16;       // width cap (can go up to 16 due to 4-bit labels & 2-bit deg packing)
// Packed frontier:
// labels: 4 bits per row in u64  (rows 0..9 -> 40 bits)
// degs:   2 bits per row in u32  (rows 0..9 -> 20 bits)

#[inline] fn get4(x:u64,i:usize)->u8 { ((x>>(i*4)) & 0xF) as u8 }
#[inline] fn set4(x:&mut u64,i:usize,v:u8){ let s=i*4; *x = (*x & !(0xFu64<<s)) | ((v as u64)<<s); }
#[inline] fn get2(x:u32,i:usize)->u8 { ((x>>(i*2)) & 0x3) as u8 }
#[inline] fn set2(x:&mut u32,i:usize,v:u8){ let s=i*2; *x = (*x & !(0x3u32<<s)) | ((v as u32)<<s); }

// Compact key representing frontier state. We implement a faster hasher below
// exploiting that the structure is already POD with limited entropy.
#[derive(Clone, Copy, Eq, PartialEq)]
struct Key {
    labels: u64,   // 4-bit ids per row; 0 means empty slot (canonicalized sequentially)
    degs:   u32,   // 2-bit degree so far per row-vertex in frontier
    ecount: u16,   // edges chosen so far
}

impl std::hash::Hash for Key {
    #[inline(always)]
    fn hash<H: Hasher>(&self, state: &mut H) {
        // Mix like a 16-byte packet. Compose into 128 bits with padding.
        // Layout (little endian): labels (64) | degs (32) | next_id (8) | ecount (16) | pad (8)
        state.write_u64(self.labels);
        let tail = (self.degs as u64)
            | ((self.ecount as u64) << 32);
        state.write_u64(tail);
    }
}

// Extremely small, fast hasher (fxhash is already good, but this avoids per-entry
// pointer chasing for BuildHasher). Fowler–Noll or a simple reversible mix.
#[derive(Default)]
struct KHasher(u64);
impl Hasher for KHasher {
    #[inline(always)] fn write(&mut self, bytes: &[u8]) { // fallback (rare)
        let mut h = self.0;
        for &b in bytes { h = h.rotate_left(5) ^ b as u64 * 0x517cc1b727220a95; }
        self.0 = h;
    }
    #[inline(always)] fn write_u64(&mut self, i: u64) {
        // Single-round reversible mix
        let mut x = i ^ 0x9e3779b97f4a7c15;
        x = (x ^ (x >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
        x = (x ^ (x >> 27)).wrapping_mul(0x94d049bb133111eb);
        self.0 ^= x;
    }
    #[inline(always)] fn finish(&self) -> u64 { self.0 }
}
type FastBuild = BuildHasherDefault<KHasher>;

mod analysis; // bring in bounds
use analysis::{upper_bound, lower_bound, lower_bound_band, upper_bound_relaxed};
mod plotly_vis; // interactive HTML plotting
mod witness;
mod transfer_util;
mod transfer; // Phase 4 transfer-matrix + Karp's max-mean cycle
mod motif; // Phase 4 motif extraction from optimal witness

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
    // Map first-seen nonzero ids to 1..k in order of appearance.
    let mut map = [0u8; 16]; // component ids limited to 4 bits
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
    // bits 1..=max_id must all be set; bit 0 ignored.
    let needed = ((1u32 << (max_id + 1)) - 2) & !1; // set bits 1..max_id
    (bit & needed) == needed && bit.count_ones() as u8 == max_id
}

#[inline(never)]
fn solve(mut m: usize, mut n: usize, beam_cap: Option<usize>, prune: bool) -> i32 {
    if m == 0 || n == 0 { return 0; }
    if m == 1 && n == 1 { return 1; }

    // transpose so width is smaller
    if m > n { std::mem::swap(&mut m, &mut n); }
    assert!(m <= MAX_M);

    // precompute grid degrees: rows = m (≤ MAX_M), cols = n (variable, can exceed MAX_M).
    // Use a flat Vec<u8> indexed via gdeg[r*n + c].
    let mut gdeg: Vec<u8> = vec![0u8; m * n];
    for r in 0..m { for c in 0..n { gdeg[r * n + c] = grid_deg(m, n, r, c); } }
    // Helper closure for legibility.
    let gd = |r: usize, c: usize| -> u8 { gdeg[r * n + c] };

    // Flatten degrees in processing (c-major, r-minor) order for fast suffix bounds.
    let pcount = m * n; // total cells
    let mut deg_list: Vec<u8> = Vec::with_capacity(pcount);
    for c in 0..n { for r in 0..m { deg_list.push(gd(r, c)); } }
    // Suffix counts of degrees 1..4 (ignore index 0). suffix_counts[p] = counts AFTER processing cell p-1 (so use p+1 after processing p).
    let mut suffix_counts: Vec<[u16;5]> = vec![[0u16;5]; pcount + 1];
    for p in (0..pcount).rev() {
        suffix_counts[p] = suffix_counts[p+1];
        let d = deg_list[p] as usize;
        if d <= 4 { suffix_counts[p][d] += 1; }
    }

    // initial frontier: column 0 before any row processed
    let mut labels0: u64 = 0;
    let mut degs0:   u32 = 0;
    for r in 0..m {
        set4(&mut labels0, r, (r as u8)+1);
        set2(&mut degs0,   r, 0);
    }
    let mut state: HashMap<Key, i32, FastBuild> =
        HashMap::with_hasher(FastBuild::default());
    state.reserve(1<<14);
    canonicalize(&mut labels0, m); // trivial but keeps invariant
    state.insert(Key{ labels:labels0, degs:degs0, ecount:0 }, 0);

    let total_v = (m*n) as u16;

    // simple admissible upper bound on future edges usable without cycles:
    // at (r,c) the remaining potential edges is
    // rem_right = m * (n-1 - c), rem_down = (m-1 - r) + (m-1)*(n-1 - c)
    let mut rem_edges_upper = vec![vec![0u16; n]; m];
    for c in 0..n {
        for r in 0..m {
            let rem_right = (n-1 - c) as u16 * m as u16;
            let rem_down_here_col = (m-1 - r) as u16;
            let rem_down_cols = (m-1) as u16 * (n-1 - c) as u16;
            rem_edges_upper[r][c] = rem_right + rem_down_here_col + rem_down_cols;
        }
    }

    // Remaining vertices after processing (r,c) (simple bound kept for reference / fallback)
    let mut rem_vertices = vec![vec![0u16; n]; m];
    for c2 in 0..n { for r2 in 0..m { rem_vertices[r2][c2] = (m - (r2+1)) as u16 + (m * (n - (c2+1))) as u16; } }

    for c in 0..n {
        for r in 0..m {
            let last_col = c + 1 == n;
            let last_row = r + 1 == m;

            // Linear position index for (r,c) in processing order
            let p_index = c * m + r;

            let mut next_state: HashMap<Key, i32, FastBuild> =
                HashMap::with_hasher(FastBuild::default());
            next_state.reserve(state.len().saturating_mul(2));
            let mut best_next_val: i32 = -1;

            for (k, preserved_so_far) in state.drain() {
                let labels = k.labels;
                let degs   = k.degs;
                let ecount     = k.ecount;

                let comp_r = get4(labels, r);
                let deg_r  = get2(degs,   r);
                let comp_down = if !last_row { get4(labels, r+1) } else { 0 };

                // choices
                // Enumerate horizontal (x) then vertical (y) decisions; hot path favors 0
                let x_max = if last_col { 0 } else { 1 };
                let y_max = if last_row { 0 } else { 1 };
                for x in 0..=x_max {
                    for y in 0..=y_max {
                        if y == 1 && comp_r != 0 && comp_r == comp_down { continue; }   // cycle
                        let deg_final = deg_r + x + y;
                        if deg_final == 0 && total_v > 1 { continue; }                  // isolation

                        // bounds pruning on edges
                        let e2 = ecount + x as u16 + y as u16;
                        let rem_up = rem_edges_upper[r][c];
                        if e2 > total_v - 1 || e2 + rem_up < total_v - 1 { continue; }

                        // mutate local copies
                        let mut labels_cur = labels;
                        let mut degs_cur   = degs;
                        let mut need_fresh = false; // whether we assign a new id when opening to the right

                        // apply vertical
                        if y == 1 {
                            merge_labels(&mut labels_cur, m, comp_r, comp_down);
                            if !last_row {
                                let d = get2(degs_cur, r+1);
                                set2(&mut degs_cur, r+1, d+1);
                            }
                        }

                        // advance frontier at row r to the right cell
                        let mut labels_next = labels_cur;
                        let mut degs_next   = degs_cur;

                        if last_col {
                            set4(&mut labels_next, r, 0);
                            set2(&mut degs_next,   r, 0);
                        } else {
                            if x == 1 {
                                // same component continues
                                set4(&mut labels_next, r, get4(labels_cur, r)); // continues same comp
                            } else {
                                // placeholder high id (15) before canonicalization
                                set4(&mut labels_next, r, 15);
                                need_fresh = true;
                            }
                            set2(&mut degs_next, r, x); // right neighbor starts with deg x
                        }

                        // forbid premature component closure
                        if comp_r != 0 && !comp_present(labels_next, m, comp_r) && !(last_col && last_row) {
                            continue;
                        }

                        // Fast-path: if extending horizontally within row (x==1) without vertical merge, and not at last_col, labels ordering preserved.
                        if !(x==1 && y==0 && !last_col) {
                            if need_fresh || !is_canonical(labels_next, m) { canonicalize(&mut labels_next, m); }
                        }

                        // score increment
                        let add_pres = (deg_final == gd(r, c)) as i32;
                        let val = preserved_so_far + add_pres;

                        let nk = Key{ labels:labels_next, degs:degs_next, ecount:e2 };
                        if prune {
                            // Degree-budget-aware preserved upper bound over remaining cells.
                            // Remaining edges budget:
                            let rem_edges_needed = (total_v - 1) - e2; // remaining edges to fill tree
                            let mut budget = (2 * rem_edges_needed as u32) as i32; // degree-sum budget
                            // Counts of degrees among remaining cells AFTER this cell
                            let counts = suffix_counts[p_index + 1];
                            let mut potential = 0i32;
                            // Iterate degrees ascending (1..4) for maximal count given budget
                            for d in 1..=4 {
                                let mut avail = counts[d] as i32;
                                if avail == 0 { continue; }
                                let fit = budget / d as i32;
                                if fit <= 0 { break; }
                                if avail > fit { avail = fit; }
                                potential += avail;
                                budget -= avail * d as i32;
                                if budget <= 0 { break; }
                            }
                            if val + potential <= best_next_val { continue; }
                        }
                        if let Some(prev) = next_state.get_mut(&nk) {
                            if val > *prev { *prev = val; if val > best_next_val { best_next_val = val; } }
                        } else {
                            next_state.insert(nk, val);
                            if val > best_next_val { best_next_val = val; }
                        }
                    }
                }
            }

            // optional beam pruning
            if let Some(cap) = beam_cap {
                if next_state.len() > cap {
                    // Partial selection without allocating a second HashMap.
                    let mut items: Vec<(Key,i32)> = next_state.into_iter().collect();
                    // nth selects element that would be at index cap after full sort.
                    items.select_nth_unstable_by(cap, |a,b| b.1.cmp(&a.1));
                    items.truncate(cap);
                    // Rebuild map with reserved capacity (=cap) for next round.
                    let mut shrunk: HashMap<Key,i32,FastBuild> = HashMap::with_capacity_and_hasher(cap, FastBuild::default());
                    for (k,v) in items { shrunk.insert(k,v); }
                    state = shrunk;
                } else { state = next_state; }
            } else { state = next_state; }
        }
    }

    // accept only empty frontier and exactly V-1 edges
    let mut ans = -1i32;
    for (k, val) in state.into_iter() {
        if k.ecount == total_v - 1 && k.labels == 0 { ans = max(ans, val); }
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
    let prune = env::var("PRUNE").map(|s| s == "1" || s.eq_ignore_ascii_case("true") ).unwrap_or(false);

    if args.len() == 3 && args[1] == "alpha" {
        let m = args[2].parse::<usize>().expect("m");
        let (alpha, cycle, graph) = transfer::compute_alpha(m);
        println!("# m={} states={} edges={} alpha={}",
                 m, graph.num_states(), graph.num_edges(), alpha);
        println!("alpha_{}_decimal = {:.10}", m, alpha.as_f64());
        println!("optimal_cycle_length = {}", cycle.len());
        for (i, &idx) in cycle.iter().enumerate() {
            let s = graph.states[idx as usize];
            println!("  step {} state_idx={} labels=0x{:x} pdeg=0x{:x}",
                     i, idx, s.labels, s.pdeg);
        }
        return;
    }
    if args.len() == 3 {
        let m = args[1].parse::<usize>().expect("m");
        let n = args[2].parse::<usize>().expect("n");
    let ans = solve(m, n, beam_cap, prune);
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
                if !first { print!(", "); } else { first = false; }
                print!("{}", v);
            }
            println!();
        }
        return;
    }
    if args.len() == 4 && args[1] == "compare" {
        let mmax = args[2].parse::<usize>().expect("mmax");
        let nmax = args[3].parse::<usize>().expect("nmax");
        let csv = env::var("CSV").map(|s| s=="1" || s.eq_ignore_ascii_case("true")).unwrap_or(false);
    if csv { println!("m,n,actual,LB_simple,LB_band,UB_cap,UB_rel,gapU_cap,gapU_rel,gapL_band,act_dens,UBcap_dens,UBrel_dens,LBband_dens"); }
    else { println!("# m n act LB_s LB_b UB_cap UB_rel gapUc gapUr gapLb act  UBc  UBr  LBb"); }
        for m in 1..=mmax {
            for n in 1..=nmax {
                let act = solve(m, n, beam_cap, prune);
                let lb_s = lower_bound(m,n) as i32;
                let lb_b = lower_bound_band(m,n) as i32;
                let ub_cap = upper_bound(m,n) as i32;
                let ub_rel = upper_bound_relaxed(m,n) as i32;
                let gap_uc = ub_cap - act;
                let gap_ur = ub_rel - act;
                let gap_lb = act - lb_b;
                let area = (m*n) as f64;
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
    if args.len() == 4 && args[1] == "plotly" {
        let csv_path = std::path::Path::new(&args[2]);
        let out_dir = std::path::Path::new(&args[3]);
        match plotly_vis::write_heatmaps(csv_path, out_dir) {
            Ok(_) => eprintln!("Plotly HTML written to {:?}", out_dir),
            Err(e) => { eprintln!("Plotly generation failed: {e}"); std::process::exit(1); }
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
                println!("# m={} n={} value={} transposed={} edges={}",
                         w.m, w.n, w.value, w.transposed, w.edges.len());
                for &((r1, c1), (r2, c2)) in &w.edges {
                    println!("{} {} {} {}", r1, c1, r2, c2);
                }
            }
            None => { println!("# empty grid (m={} n={})", m, n); }
        }
        return;
    }
    eprintln!("Usage:");
    eprintln!("  {} m n", args[0]);
    eprintln!("  {} table M N", args[0]);
    eprintln!("  {} compare M N   # empirical vs bounds", args[0]);
    eprintln!("  {} plotly results.csv out_dir  # generate interactive HTML plots", args[0]);
    eprintln!("  {} witness M N   # print one optimal spanning tree (edges)", args[0]);
    eprintln!("  {} alpha M      # Phase 4: max-mean cycle on transfer graph (m <= 6)", args[0]);
    eprintln!("  {} motif M N    # Phase 4: visualize optimal witness and detect period", args[0]);
    eprintln!("Env: BEAM=<cap>  # optional beam size",);
    eprintln!("     PRUNE=1      # enable heuristic pruning");
    eprintln!("     CSV=1        # CSV output for compare mode");
}
