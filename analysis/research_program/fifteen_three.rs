//! Three overlapping nine-row forests. Messages on six common rows cancel
//! exactly; every integer sweep supplies a bound even without convergence.
use super::{phase, spread, Graph, PH};
use std::collections::BTreeMap;
const INF: i64 = 1 << 60;
struct Band {
    w: Vec<Vec<i64>>,
    sig: [Vec<usize>; 2],
    msg: [Vec<Vec<i64>>; 2],
    suf: Vec<Vec<i64>>,
}
impl Band {
    fn new(g: &Graph<9>, price: &[i64], width: usize, sig: &[Vec<usize>; 2]) -> Self {
        let mut w = vec![vec![0; g.dest.len()]; PH];
        for (i, &(a, b, _)) in g.st.iter().enumerate() {
            for k in g.off[i]..g.off[i + 1] {
                let c = g.st[g.dest[k] as usize].1;
                for r in 0..7 {
                    let z = 512 * r + spread(a >> r) + 2 * spread(b >> r) + 4 * spread(c >> r);
                    for h in 0..PH {
                        w[h][k] += price[h * 3584 + z]
                    }
                }
            }
        }
        Self {
            w,
            sig: sig.clone(),
            msg: std::array::from_fn(|_| vec![vec![0; width]; 109]),
            suf: vec![vec![0; g.st.len()]; 110],
        }
    }
    fn relax(&mut self, g: &Graph<9>, j: usize) {
        let (u, v) = self.suf.split_at_mut(j + 1);
        let h = phase(j.saturating_sub(2));
        for (i, z) in u[j].iter_mut().enumerate() {
            *z = (g.off[i]..g.off[i + 1])
                .map(|k| {
                    v[0][g.dest[k] as usize]
                        + self.msg[0][j][self.sig[0][k]]
                        + self.msg[1][j][self.sig[1][k]]
                        + if j < 2 { 0 } else { self.w[h][k] }
                })
                .min()
                .unwrap()
        }
    }
    fn forward(&self, g: &Graph<9>, j: usize, f: &[i64], side: Option<usize>) -> Vec<i64> {
        let h = phase(j.saturating_sub(2));
        let mut v = vec![INF; side.map_or(g.st.len(), |t| self.msg[t][j].len())];
        for (i, &z) in f.iter().enumerate() {
            if z == INF {
                continue;
            }
            for k in g.off[i]..g.off[i + 1] {
                let d = g.dest[k] as usize;
                let mut t = z
                    + self.msg[0][j][self.sig[0][k]]
                    + self.msg[1][j][self.sig[1][k]]
                    + if j < 2 { 0 } else { self.w[h][k] };
                let id = if let Some(s) = side {
                    t += self.suf[j + 1][d];
                    self.sig[s][k]
                } else {
                    d
                };
                v[id] = v[id].min(t);
            }
        }
        v
    }
}
pub(super) fn price(p: &[i64], budget: i64) {
    let g = Graph::<9>::new();
    let n = PH * 3584;
    let mut ids = BTreeMap::new();
    let mut sig: [Vec<usize>; 2] = std::array::from_fn(|_| vec![0; g.dest.len()]);
    for (i, &(a, b, _)) in g.st.iter().enumerate() {
        for k in g.off[i]..g.off[i + 1] {
            let c = g.st[g.dest[k] as usize].1;
            for (s, v) in sig.iter_mut().enumerate() {
                let sh = s * 3;
                let key = ((a >> sh) & 63, (b >> sh) & 63, (c >> sh) & 63);
                let id = ids.len();
                v[k] = *ids.entry(key).or_insert(id)
            }
        }
    }
    let mut bands: Vec<_> = [&p[..n], &vec![0; n], &p[n..]]
        .iter()
        .map(|v| Band::new(&g, v, ids.len(), &sig))
        .collect();
    for band in &mut bands {
        for j in (0..109).rev() {
            band.relax(&g, j)
        }
    }
    let mut best = bands.iter().map(|b| b.suf[0][0]).sum::<i64>();
    let rounds = std::env::var("STRIP_THREE_ROUNDS")
        .ok()
        .and_then(|x| x.parse().ok())
        .unwrap_or(6);
    for i in 0..rounds {
        let mut fw = vec![vec![INF; g.st.len()]; 3];
        for f in &mut fw {
            f[0] = 0
        }
        for j in 0..109 {
            for k0 in 0..2 {
                let k = if i % 2 == 0 { k0 } else { 1 - k0 };
                let u = bands[k].forward(&g, j, &fw[k], Some(1));
                let v = bands[k + 1].forward(&g, j, &fw[k + 1], Some(0));
                let a = *u.iter().min().unwrap();
                let b = *v.iter().min().unwrap();
                for t in 0..ids.len() {
                    if u[t] != INF && v[t] != INF {
                        let m = (bands[k].msg[1][j][t] + ((v[t] - b) - (u[t] - a)) / 2)
                            .clamp(-INF / 10000, INF / 10000);
                        bands[k].msg[1][j][t] = m;
                        bands[k + 1].msg[0][j][t] = -m;
                    }
                }
            }
            for k in 0..3 {
                fw[k] = bands[k].forward(&g, j, &fw[k], None)
            }
        }
        for band in &mut bands {
            for j in (0..109).rev() {
                band.relax(&g, j)
            }
        }
        best = best.max(bands.iter().map(|b| b.suf[0][0]).sum());
        eprintln!("three-strip sweep {i}: {best}, target {budget}");
        if best > budget {
            break;
        }
    }
    if std::env::args().nth(2).as_deref() == Some("uniform3") {
        let steady = std::env::var("STRIP_STEADY")
            .ok()
            .and_then(|s| s.parse::<usize>().ok());
        let mut fw = vec![vec![INF; g.st.len()]; 3];
        for f in &mut fw {
            f[0] = 0
        }
        let mut prev = vec![fw.clone(); 3];
        let mut delta = (-INF, 0);
        for j in 0..109 {
            for k in 0..3 {
                fw[k] = bands[k].forward(&g, j, &fw[k], None)
            }
            if steady == Some(j) {
                assert!((18..90).contains(&j));
                let mut v = fw.clone();
                for t in 0..90 {
                    let mut w = v.clone();
                    for col in j + 1..=j + 3 {
                        for k in 0..3 {
                            w[k] = bands[k].forward(&g, col, &w[k], None)
                        }
                    }
                    let mut rate = 0;
                    let mut intercept = 0;
                    for k in 0..3 {
                        rate += w[k].iter().zip(&v[k]).map(|(a, b)| a - b).min().unwrap();
                        let off = v[k].iter().zip(&fw[k]).map(|(a, b)| a - b).max().unwrap();
                        intercept += v[k]
                            .iter()
                            .zip(&bands[k].suf[j + 1])
                            .map(|(a, b)| a + b - off)
                            .min()
                            .unwrap();
                    }
                    if t % 10 == 0 || t == 89 {
                        eprintln!("steady {j} {t}: {intercept} {rate}")
                    }
                    if t == 89 {
                        // Greatest subeigenvector below the actual prefix,
                        // instead of applying a uniform penalty for a state
                        // that might never attain the whole-word price.
                        rate = 0;
                        intercept = 0;
                        for k in 0..3 {
                            let step = w[k].iter().zip(&v[k]).map(|(a, b)| a - b).min().unwrap();
                            let mut pot = fw[k].clone();
                            for _ in 0..128 {
                                let mut nv = pot.clone();
                                for jj in j + 1..=j + 3 {
                                    nv = bands[k].forward(&g, jj, &nv, None)
                                }
                                let mut diff = false;
                                for (a, b) in pot.iter_mut().zip(nv) {
                                    if b - step < *a {
                                        diff = true;
                                        *a = b - step
                                    }
                                }
                                if !diff {
                                    break;
                                }
                            }
                            let mut nv = pot.clone();
                            for jj in j + 1..=j + 3 {
                                nv = bands[k].forward(&g, jj, &nv, None)
                            }
                            rate += nv.iter().zip(&pot).map(|(a, b)| a - b).min().unwrap();
                            intercept += pot
                                .iter()
                                .zip(&bands[k].suf[j + 1])
                                .map(|(a, b)| a + b)
                                .min()
                                .unwrap();
                        }
                        println!("{intercept} {rate} {j}");
                        return;
                    }
                    v = w;
                }
            }
            if (18..90).contains(&j) {
                let old = &prev[j % 3];
                let mut dif = 0;
                for k in 0..3 {
                    dif += fw[k]
                        .iter()
                        .zip(&old[k])
                        .map(|(&a, &b)| {
                            assert!(a != INF && b != INF);
                            a - b
                        })
                        .min()
                        .unwrap()
                }
                delta = delta.max((dif, j))
            }
            prev[j % 3] = fw.clone();
        }
        let val: i64 = fw.iter().map(|v| v.iter().min().unwrap()).sum();
        println!("{val} {} {}", delta.0, delta.1);
        return;
    }
    if best > budget {
        println!("{best} 0");
        return;
    }
    joined(&g, &bands, budget, best);
}

fn joined(g: &Graph<9>, bs: &[Band], budget: i64, dual: i64) {
    use std::collections::HashMap;
    let base = bs.iter().map(|b| b.suf[0][0]).sum::<i64>();
    let extra = budget - base;
    let start = ([0u32; 3], std::array::from_fn::<_, 15, _>(|i| i as u8));
    let mut dp = HashMap::from([(start, 0i64)]);
    let mut dropped = extra + 1;
    let mut count = 0u64;
    let paths = std::env::args().nth(2).as_deref() == Some("threepaths");
    let mut history = Vec::new();
    for j in 0usize..109 {
        let h = phase(j.saturating_sub(2));
        let mut nd = HashMap::new();
        let mut cache: Vec<HashMap<u32, Vec<(u16, u32, i64)>>> = vec![HashMap::new(); 3];
        let mut memo = HashMap::new();
        let mut pred = HashMap::new();
        for (&(idx, part), &z) in &dp {
            if z >= dropped {
                continue;
            }
            for t in 0..3 {
                cache[t].entry(idx[t]).or_insert_with(|| {
                    let i = idx[t] as usize;
                    let b = &bs[t];
                    (g.off[i]..g.off[i + 1])
                        .filter_map(|k| {
                            let d = g.dest[k];
                            let w = b.msg[0][j][b.sig[0][k]]
                                + b.msg[1][j][b.sig[1][k]]
                                + if j < 2 { 0 } else { b.w[h][k] };
                            let v = w + b.suf[j + 1][d as usize] - b.suf[j][i];
                            assert!(v >= 0);
                            (v <= extra).then_some((g.st[d as usize].1, d, v))
                        })
                        .collect()
                });
            }
            let b = g.st[idx[0] as usize].1 | (g.st[idx[2] as usize].1 << 6);
            for &(m, md, mw) in &cache[1][&idx[1]] {
                for &(a, ad, aw) in &cache[0][&idx[0]] {
                    let u = z + mw + aw;
                    if a >> 3 != m & 63 || u >= dropped {
                        continue;
                    }
                    for &(c, cd, cw) in &cache[2][&idx[2]] {
                        let v = u + cw;
                        if c & 63 != m >> 3 || v >= dropped {
                            continue;
                        }
                        let full = a | (c << 6);
                        count += 1;
                        if let Some(p) = *memo
                            .entry((part, b, full))
                            .or_insert_with(|| super::step(part, b, full))
                        {
                            let dest = ([ad, md, cd], p);
                            let e = nd.entry(dest).or_insert(INF);
                            if v < *e {
                                *e = v;
                                if paths {
                                    pred.insert(dest, (idx, part, full));
                                }
                            }
                        }
                    }
                }
            }
            if nd.len() > 120000 {
                let mut v: Vec<_> = nd.values().copied().collect();
                v.select_nth_unstable(60000);
                dropped = dropped.min(v[60000]);
                nd.retain(|_, z| *z < dropped)
            }
            if memo.len() > 200000 {
                memo.clear()
            }
        }
        if paths {
            pred.retain(|s, _| nd.contains_key(s));
            history.push(pred)
        }
        dp = nd;
        if dp.is_empty() {
            break;
        }
    }
    let best = dual.max(base + dropped.min(dp.values().min().copied().unwrap_or(INF)));
    println!("{best} {count}");
    if paths && history.len() == 109 {
        let mut out: Vec<_> = dp.iter().collect();
        out.sort_unstable_by_key(|(s, v)| (**v, **s));
        let mut printed = std::collections::HashSet::new();
        for (&end, _) in out.iter().take(16).copied() {
            let mut d = end;
            for j in (0..109).rev() {
                let (i, p, c) = history[j][&d];
                d = (i, p);
                let (a, b, _) = g.st[i[0] as usize];
                let (aa, bb, _) = g.st[i[2] as usize];
                let a = a | (aa << 6);
                let b = b | (bb << 6);
                let pat = p.iter().rev().fold(0u64, |x, &z| x * 16 + u64::from(z));
                if printed.insert((j, a, b, pat, c)) {
                    println!("{j} {a} {b} {pat} {c}")
                }
            }
        }
    }
}
