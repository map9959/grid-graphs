// Exact bounded pricing on a 13-row strip. Two nine-row projections give
// suffix lower bounds; prune only if both bounds together exceed the budget.
use std::collections::HashMap;
use std::io::{self, Read};
#[cfg(fifteen)]
mod fifteen_three;
type Part<const N: usize> = [u8; N];
const H: usize = if cfg!(fifteen) {
    15
} else if cfg!(fourteen) {
    14
} else {
    13
};
const BOT: usize = if cfg!(wider) { 10 } else { 9 };
const TOP: usize = if cfg!(wide_top) { 10 } else { 9 };
const O: usize = H - BOT;
const CM: usize = (1 << (TOP - O)) - 1;
const PH: usize = 2 * H - 1;
fn union(p: &mut [u8; 2 * H], a: usize, b: usize) -> bool {
    let root = |mut x: usize| {
        while p[x] as usize != x {
            x = p[x] as usize
        }
        x
    };
    let x = root(a);
    let y = root(b);
    p[x] = y as u8;
    x != y
}
fn step<const N: usize>(part: Part<N>, b: u16, c: u16) -> Option<Part<N>> {
    let mut p: [u8; 2 * H] = std::array::from_fn(|i| i as u8);
    p[..N].copy_from_slice(&part);
    for i in 0..N {
        if (b | c) >> i & 1 != 0 && !union(&mut p, i, N + i) {
            return None;
        }
        if i + 1 < N && (c | c >> 1) >> i & 1 != 0 && !union(&mut p, N + i, N + i + 1) {
            return None;
        }
    }
    let roots: Part<N> = std::array::from_fn(|i| {
        let mut x = N + i;
        while p[x] as usize != x {
            x = p[x] as usize
        }
        x as u8
    });
    Some(std::array::from_fn(|i| {
        roots.iter().position(|x| *x == roots[i]).unwrap() as u8
    }))
}
fn phase(j: usize) -> usize {
    match j {
        11 if H >= 14 => 25,
        95 if H >= 14 => 26,
        12 if H >= 15 => 27,
        94 if H >= 15 => 28,
        8 => 19,
        98 => 20,
        9 => 21,
        97 => 22,
        10 => 23,
        96 => 24,
        0..=7 => j,
        99.. => j - 88,
        _ => 8 + (j - 8) % 3,
    }
}
fn spread(x: u16) -> usize {
    ((x & 1) + ((x & 2) << 2) + ((x & 4) << 4)) as usize
}
struct Graph<const N: usize> {
    st: Vec<(u16, u16, Part<N>)>,
    dest: Vec<u32>,
    off: Vec<usize>,
}
impl<const N: usize> Graph<N> {
    fn new() -> Self {
        let init = (0u16, 0u16, std::array::from_fn(|i| i as u8));
        let mut st = vec![init];
        let mut ids = HashMap::from([(init, 0)]);
        let mut memo = HashMap::new();
        let mut dest = Vec::new();
        let mut off = vec![0];
        let mut i = 0;
        while i < st.len() {
            let (_, b, p) = st[i];
            for &(c, q) in memo
                .entry((b, p))
                .or_insert_with(|| {
                    (0..1 << N)
                        .filter_map(|c| step(p, b, c).map(|q| (c, q)))
                        .collect::<Vec<_>>()
                })
                .iter()
            {
                dest.push(*ids.entry((b, c, q)).or_insert_with(|| {
                    st.push((b, c, q));
                    (st.len() - 1) as u32
                }))
            }
            off.push(dest.len());
            i += 1
        }
        Self { st, dest, off }
    }
}
struct Projection {
    weights: Vec<Vec<i64>>,
    suffix: Vec<Vec<i64>>,
    sig: Vec<usize>,
    msg: Vec<Vec<i64>>,
    order: Vec<usize>,
    init: Vec<i64>,
}
// Split at columns 53,54. Forward and reversed halves end on opposite
// orders of the same pair. Their terminal prices cancel on any full word.
fn split_projection<const N: usize>(
    g: &Graph<N>,
    p: &[i64],
    reverse: &[i64],
    shift: usize,
    first: usize,
    right: bool,
    outward: bool,
) -> Projection {
    let mut left = Projection::new(g, p, shift, first);
    let mut other = Projection::new(g, reverse, shift, first);
    const INF: i64 = 1 << 60;
    let end = |t: &Projection, len: usize| {
        let mut v = vec![INF; g.st.len()];
        v[0] = 0;
        for j in 0..len {
            v = t.forward(g, j, &v, false)
        }
        let mut tab = HashMap::new();
        for (i, &(a, b, _)) in g.st.iter().enumerate() {
            let z = tab.entry((a, b)).or_insert(INF);
            *z = (*z).min(v[i])
        }
        tab
    };
    let f = end(&left, 55);
    let r = end(&other, 56);
    if outward {
        let (pr, len) = if right {
            (&mut left, 56)
        } else {
            (&mut other, 55)
        };
        pr.suffix.truncate(len + 1);
        pr.suffix[len].fill(0);
        for j in 2..len {
            pr.order[j] = phase(109 - len + j - 2)
        }
        for (i, &(a, b, _)) in g.st.iter().enumerate() {
            let (a, b) = if right { (a, b) } else { (b, a) };
            let v = f.get(&(a, b)).copied().unwrap_or(INF);
            let w = r.get(&(b, a)).copied().unwrap_or(INF);
            let q = if w == INF || v == INF { 0 } else { (w - v) / 2 };
            pr.init[i] = if right { -q } else { q }
        }
        pr.rebuild(g);
        return if right { left } else { other };
    }
    let (pr, len) = if right {
        (&mut other, 56)
    } else {
        (&mut left, 55)
    };
    pr.suffix.truncate(len + 1);
    for (i, &(a, b, _)) in g.st.iter().enumerate() {
        let (a, b) = if right { (b, a) } else { (a, b) };
        let v = f.get(&(a, b)).copied().unwrap_or(INF);
        let w = r.get(&(b, a)).copied().unwrap_or(INF);
        let q = if w == INF || v == INF { 0 } else { (w - v) / 2 };
        pr.suffix[len][i] = if right { -q } else { q };
    }
    pr.rebuild(g);
    if right {
        other
    } else {
        left
    }
}
impl Projection {
    fn middle<const N: usize>(&mut self, g: &Graph<N>, rev: Projection, width: usize) {
        assert!(width >= 5 && width < 100);
        let mut fw = vec![1i64 << 60; g.st.len()];
        fw[0] = 0;
        for j in 0..width {
            fw = rev.forward(g, j, &fw, false)
        }
        let mut tab = HashMap::new();
        for (i, &(b, a, _)) in g.st.iter().enumerate() {
            let z = tab.entry((a, b)).or_insert(1i64 << 60);
            *z = (*z).min(fw[i])
        }
        // Independent left and right boundary segments, with the final
        // two columns shared with the central word. Discard connections
        // made by those segments when starting the central forest.
        let len = 113 - 2 * width;
        self.suffix.truncate(len + 1);
        for (i, &(a, b, _)) in g.st.iter().enumerate() {
            self.suffix[len][i] = tab[&(a, b)]
        }
        // This helper uses *reflected prices* for the right segment.
        // Computing a separate left table below does not assume symmetry.
        fw.fill(1i64 << 60);
        fw[0] = 0;
        for j in 0..width {
            fw = self.forward(g, j, &fw, false)
        }
        tab.clear();
        for (i, &(a, b, _)) in g.st.iter().enumerate() {
            let z = tab.entry((a, b)).or_insert(1i64 << 60);
            *z = (*z).min(fw[i])
        }
        for (i, &(a, b, _)) in g.st.iter().enumerate() {
            self.init[i] = tab[&(a, b)]
        }
        for j in 2..len {
            self.order[j] = phase(width + j - 4)
        }
        self.rebuild(g);
    }
    fn new<const N: usize>(g: &Graph<N>, price: &[i64], shift: usize, first: usize) -> Self {
        let mut weights = vec![vec![0; g.dest.len()]; PH];
        let mut sig = vec![0; g.dest.len()];
        for (i, &(a, b, _)) in g.st.iter().enumerate() {
            for k in g.off[i]..g.off[i + 1] {
                let c = g.st[g.dest[k] as usize].1;
                sig[k] = (((a as usize >> shift) & CM) << 10)
                    | (((b as usize >> shift) & CM) << 5)
                    | ((c as usize >> shift) & CM);
                let ids: [usize; 7] = std::array::from_fn(|r| {
                    512 * r
                        + spread(a >> (r + first))
                        + 2 * spread(b >> (r + first))
                        + 4 * spread(c >> (r + first))
                });
                for h in 0..PH {
                    weights[h][k] = ids.iter().map(|&z| price[3584 * h + z]).sum()
                }
            }
        }
        let mut suffix = vec![vec![0i64; g.st.len()]];
        for j in (0usize..109).rev() {
            let v = suffix.last().unwrap();
            let h = phase(j.saturating_sub(2));
            let next = (0..g.st.len())
                .map(|i| {
                    (g.off[i]..g.off[i + 1])
                        .map(|k| v[g.dest[k] as usize] + if j < 2 { 0 } else { weights[h][k] })
                        .min()
                        .unwrap()
                })
                .collect();
            suffix.push(next)
        }
        suffix.reverse();
        Self {
            weights,
            suffix,
            sig,
            msg: vec![vec![0; 32768]; 109],
            order: (0usize..109).map(|j| phase(j.saturating_sub(2))).collect(),
            init: vec![0; g.st.len()],
        }
    }
    fn rebuild<const N: usize>(&mut self, g: &Graph<N>) {
        for j in (0usize..self.suffix.len() - 1).rev() {
            let h = self.order[j];
            let (left, right) = self.suffix.split_at_mut(j + 1);
            for i in 0..g.st.len() {
                left[j][i] = (g.off[i]..g.off[i + 1])
                    .map(|k| {
                        right[0][g.dest[k] as usize]
                            + self.msg[j][self.sig[k]]
                            + if j == 1 {
                                self.init[g.dest[k] as usize]
                            } else if j == 0 {
                                0
                            } else {
                                self.weights[h][k]
                            }
                    })
                    .min()
                    .unwrap()
            }
        }
    }
    fn forward<const N: usize>(&self, g: &Graph<N>, j: usize, fw: &[i64], marg: bool) -> Vec<i64> {
        const INF: i64 = 1 << 60;
        let mut z = vec![INF; if marg { 32768 } else { g.st.len() }];
        let h = self.order[j];
        for (i, &v) in fw.iter().enumerate() {
            if v == INF {
                continue;
            }
            for k in g.off[i]..g.off[i + 1] {
                let d = g.dest[k] as usize;
                let s = self.sig[k];
                let u =
                    v + (if j == 1 {
                        self.init[d]
                    } else if j == 0 {
                        0
                    } else {
                        self.weights[h][k]
                    }) + self.msg[j][s];
                if marg {
                    z[s] = z[s].min(u + self.suffix[j + 1][d])
                } else {
                    z[d] = z[d].min(u)
                }
            }
        }
        z
    }
    fn opts<const N: usize>(
        &self,
        g: &Graph<N>,
        j: usize,
        i: u32,
        delta: i64,
    ) -> Vec<(u16, u32, i64)> {
        let h = self.order[j];
        let i = i as usize;
        (g.off[i]..g.off[i + 1])
            .filter_map(|k| {
                let d = g.dest[k];
                let w = self.msg[j][self.sig[k]]
                    + if j == 1 {
                        self.init[d as usize]
                    } else if j == 0 {
                        0
                    } else {
                        self.weights[h][k]
                    };
                let z = w + self.suffix[j + 1][d as usize] - self.suffix[j][i];
                assert!(z >= 0);
                if z <= delta {
                    Some((g.st[d as usize].1, d, z))
                } else {
                    None
                }
            })
            .collect()
    }
}
fn main() {
    let budget: i64 = std::env::args().nth(1).unwrap().parse().unwrap();
    let mode = std::env::args().nth(2);
    let witness =
        mode.as_deref() == Some("witness") || (H == 15 && mode.as_deref() == Some("beam"));
    let beam = mode.as_deref() == Some("beam") || witness;
    let paths = mode.as_deref() == Some("paths") || witness;
    let emit = mode.as_deref() == Some("emit") || (beam && !witness);
    const INF: i64 = 1 << 60;
    let mut text = String::new();
    io::stdin().read_to_string(&mut text).unwrap();
    let p: Vec<i64> = text
        .split_whitespace()
        .map(|v| v.parse().unwrap())
        .collect();
    let n = PH * 3584;
    assert_eq!(p.len(), 2 * n);
    assert!(p.iter().all(|v| v.unsigned_abs() < (INF / 10000) as u64));
    #[cfg(fifteen)]
    if matches!(
        mode.as_deref(),
        Some("three") | Some("threepaths") | Some("uniform3")
    ) {
        fifteen_three::price(&p, budget);
        return;
    }
    let g = Graph::<TOP>::new();
    let gh = Graph::<BOT>::new();
    assert!(CM <= 31);
    let outward = matches!(mode.as_deref(), Some("outleft") | Some("outright"));
    let right = matches!(mode.as_deref(), Some("right") | Some("outright"));
    let half = right || outward || mode.as_deref() == Some("left");
    let mid = mode.as_deref() == Some("middle");
    let len = if mid {
        113 - 2 * 10
    } else if half {
        if right {
            56
        } else {
            55
        }
    } else {
        109
    };
    let reversed = |t: &[i64]| {
        let mut rev = vec![0; t.len()];
        for j in 0..107 {
            for r in 0..7 {
                for m in 0..512 {
                    let mr = ((m & 73) << 2) | (m & 146) | ((m & 292) >> 2);
                    rev[(phase(j) * 7 + r) * 512 + m] = t[(phase(106 - j) * 7 + r) * 512 + mr]
                }
            }
        }
        rev
    };
    let mut lo = if half {
        split_projection(&g, &p[..n], &reversed(&p[..n]), O, 0, right, outward)
    } else {
        Projection::new(&g, &p[..n], O, 0)
    };
    let mut hi = if half {
        split_projection(&gh, &p[n..], &reversed(&p[n..]), 0, BOT - 9, right, outward)
    } else {
        Projection::new(&gh, &p[n..], 0, BOT - 9)
    };
    if mid {
        lo.middle(&g, Projection::new(&g, &reversed(&p[..n]), O, 0), 10);
        hi.middle(
            &gh,
            Projection::new(&gh, &reversed(&p[n..]), 0, BOT - 9),
            10,
        );
    }
    let rounds = std::env::var("PRICE13_SWEEPS")
        .ok()
        .map(|s| s.parse::<usize>().unwrap())
        .unwrap_or(2);
    for _ in 0..rounds {
        if lo.suffix[0][0] + hi.suffix[0][0] > budget {
            break;
        }
        let mut a = vec![INF; g.st.len()];
        a[0] = 0;
        let mut b = vec![INF; gh.st.len()];
        b[0] = 0;
        for j in 0..len {
            let ma = lo.forward(&g, j, &a, true);
            let mb = hi.forward(&gh, j, &b, true);
            let za = *ma.iter().min().unwrap();
            let zb = *mb.iter().min().unwrap();
            for t in 0..32768 {
                if ma[t] != INF && mb[t] != INF {
                    let diff = ((mb[t] - zb) - (ma[t] - za)) / 2;
                    let v = (lo.msg[j][t] + diff).clamp(-INF / 10000, INF / 10000);
                    lo.msg[j][t] = v;
                    hi.msg[j][t] = -v
                }
            }
            a = lo.forward(&g, j, &a, false);
            b = hi.forward(&gh, j, &b, false)
        }
        lo.rebuild(&g);
        hi.rebuild(&gh)
    }
    let base = lo.suffix[0][0] + hi.suffix[0][0];
    let extra = if beam { INF / 4 } else { budget - base };
    if extra < 0 {
        println!("{base} 0");
        return;
    }
    let slices = std::env::var("STRIP_SLICES")
        .ok()
        .map(|s| s.parse::<usize>().unwrap())
        .unwrap_or(1);
    let seed = std::env::var("STRIP_SEED")
        .ok()
        .and_then(|s| s.parse::<u64>().ok())
        .unwrap_or(0);
    assert!(slices.is_power_of_two() && slices <= 256 && (slices == 1 || (!paths && !emit)));
    let mut all_best = INF;
    let mut all_count = 0;
    for slice in 0..slices {
        type State = (u32, u32, Part<H>);
        let start: State = (0, 0, std::array::from_fn(|i| i as u8));
        let mut dp = HashMap::from([(start, 0)]);
        let mut count = 0u64;
        let mut layers = Vec::new();
        let mut dropped = INF;
        let trace = std::env::var_os("STRIP_TRACE").is_some();
        let state_limit = std::env::var("STRIP_LIMIT")
            .ok()
            .and_then(|s| s.parse::<usize>().ok())
            .unwrap_or(60000)
            .clamp(8000, 800000);
        for j in 0..len {
            let prefix_floor = dp.values().min().copied().unwrap_or(INF).min(dropped);
            let mut next = HashMap::new();
            let mut pred = HashMap::new();
            let mut ca = HashMap::new();
            let mut cb = HashMap::new();
            let mut memo = HashMap::new();
            let mut arcs = Vec::new();
            let mut visits = 0u64;
            let keep = if witness {
                std::env::var("STRIP_WITNESSES")
                    .ok()
                    .and_then(|s| s.parse().ok())
                    .unwrap_or(96)
            } else {
                std::env::var("PRICE13_BEAM")
                    .ok()
                    .and_then(|s| s.parse().ok())
                    .unwrap_or(16usize)
            };
            let mut cap = extra;
            for (&s, &z) in &dp {
                let (ia, ib, part) = s;
                let b = g.st[ia as usize].1 | (gh.st[ib as usize].1 << O);
                let low = ca.entry(ia).or_insert_with(|| lo.opts(&g, j, ia, extra));
                let high = cb.entry(ib).or_insert_with(|| {
                    let mut by: [Vec<(u16, u32, i64)>; 32] = std::array::from_fn(|_| Vec::new());
                    for v in hi.opts(&gh, j, ib, extra) {
                        by[v.0 as usize & CM].push(v)
                    }
                    for v in &mut by {
                        v.sort_unstable_by_key(|x| x.2)
                    }
                    by
                });
                let rem = (if beam || H < 14 {
                    cap
                } else {
                    extra.min(dropped - 1)
                }) - z;
                for &(a, da, wa) in low.iter() {
                    if wa > rem {
                        continue;
                    }
                    for &(c, db, wb) in high[(a >> O) as usize].iter() {
                        visits += 1;
                        if wa + wb > rem {
                            break;
                        }
                        let full = a | (c << O);
                        if slices > 1 && j == 1 && {
                            let mut z = u64::from(full) | (u64::from(b) << 16);
                            z ^= z >> 16;
                            z = z.wrapping_mul(0x85ebca6b);
                            z ^= z >> 13;
                            (z as usize & (slices - 1)) != slice
                        } {
                            continue;
                        }
                        if let Some(q) = *memo
                            .entry((b, part, full))
                            .or_insert_with(|| step(part, b, full))
                        {
                            let d = (da, db, q);
                            let v = z + wa + wb;
                            count += 1;
                            let u = next.entry(d).or_insert(v);
                            if paths && v <= *u {
                                pred.insert(d, (s, full));
                            }
                            *u = (*u).min(v);
                            if emit {
                                arcs.push((s, d, full))
                            }
                        }
                    }
                }
                if witness && next.len() > 4 * keep {
                    let mut vals: Vec<_> = next.values().copied().collect();
                    vals.select_nth_unstable(keep);
                    cap = cap.min(vals[keep]);
                    next.retain(|_, v| *v <= cap);
                    pred.retain(|s, _| next.contains_key(s));
                }
                if H >= 14 && !beam && next.len() > state_limit {
                    let mut vals: Vec<_> = next.values().copied().collect();
                    let cut = state_limit / 3;
                    vals.select_nth_unstable(cut);
                    dropped = dropped.min(vals[cut]);
                    if trace {
                        eprintln!("trim layer {j}: dropped {dropped} extra {extra}")
                    }
                    next.retain(|_, v| *v < dropped);
                    pred.retain(|s, _| next.contains_key(s));
                }
                if memo.len() > 300000 {
                    memo.clear()
                }
                if next.len() > state_limit.max(250000)
                    || (emit && !beam && count > 1000000)
                    || visits > 240000000
                {
                    if !emit {
                        dropped = dropped.min(prefix_floor);
                        next.clear();
                        break;
                    }
                    eprintln!("pricing budget too wide at layer {j}");
                    std::process::exit(2)
                }
            }
            if beam && next.len() > keep {
                let mut vs: Vec<_> = next
                    .iter()
                    .map(|(&s, &v)| {
                        let mut t = u64::from(s.0) ^ (u64::from(s.1) << 32) ^ seed;
                        t ^= t >> 30;
                        t = t.wrapping_mul(0xbf58476d1ce4e5b9);
                        t ^= t >> 27;
                        (v, if seed == 0 { 0 } else { t }, s)
                    })
                    .collect();
                vs.select_nth_unstable(keep);
                vs.truncate(keep);
                next = vs.into_iter().map(|(v, _, s)| (s, v)).collect();
                arcs.retain(|(_, d, _)| next.contains_key(d));
                pred.retain(|s, _| next.contains_key(s));
            }
            if emit {
                layers.push(arcs)
            }
            if paths {
                layers.push(pred.into_iter().map(|(d, (s, c))| (s, d, c)).collect())
            }
            dp = next;
            if trace {
                eprintln!(
                    "layer {j}: states {} visited {visits} base {base} dropped {dropped}",
                    dp.len()
                )
            }
            if dp.is_empty() {
                break;
            }
        }
        let best = dp
            .values()
            .min()
            .map_or(budget + 1, |z| base + z)
            .min(base + dropped);
        all_best = all_best.min(best);
        all_count += count;
        if slices == 1 {
            println!("{best} {count}")
        }
        if slices > 1 && best <= budget && dp.values().any(|&v| base + v == best) {
            println!("{base} {all_count}");
            return;
        }
        if (emit || paths) && !dp.is_empty() {
            use std::collections::HashSet;
            let dpmin = *dp.values().min().unwrap();
            let mut live: HashSet<_> = dp
                .iter()
                .filter_map(|(s, v)| (!paths || witness || *v <= dpmin + 1000000).then_some(*s))
                .collect();
            for (j, arcs) in layers.into_iter().enumerate().rev() {
                let mut prev = HashSet::new();
                let mut lines = HashSet::new();
                for (s, d, c) in arcs {
                    if live.contains(&d) {
                        prev.insert(s);
                        let (i, k, p) = s;
                        let (a, b, _) = g.st[i as usize];
                        let (x, y, _) = gh.st[k as usize];
                        let bits = p.iter().rev().fold(0u64, |v, &z| 16 * v + z as u64);
                        lines.insert((a | (x << O), b | (y << O), bits, c));
                    }
                }
                for (a, b, p, c) in lines {
                    println!("{j} {a} {b} {p} {c}")
                }
                live = prev;
            }
        }
    }
    if slices > 1 {
        println!("{all_best} {all_count}")
    }
}
