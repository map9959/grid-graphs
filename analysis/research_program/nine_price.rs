// Exact integer path pricing. stdin: P*(H-2)*512 prices,
// phase-major. Optional argument: output arcs within this regret of optimum.
use std::{
    collections::{HashMap, HashSet},
    io::{self, BufWriter, Read, Write},
};
const H: usize = if cfg!(eleven) { 11 } else if cfg!(seven){7}else { 9 };
const P: usize = if cfg!(phase13) {
    25
} else if cfg!(eleven) {
    21
} else {
    19
};
type Part = [u8; H];
type State = (u16, u16, Part);
fn root(p: &[u8; 2 * H], mut i: usize) -> usize {
    while p[i] as usize != i {
        i = p[i] as usize
    }
    i
}
fn advance(b: u16, part: Part, c: u16) -> Option<Part> {
    let mut p = std::array::from_fn(|i| i as u8);
    p[..H].copy_from_slice(&part);
    for i in 0..H {
        for (a, z, on) in [
            (i, i + H, ((b | c) >> i) & 1 != 0),
            (
                i + H,
                i + H + 1,
                i + 1 < H && ((c | (c >> 1)) >> i) & 1 != 0,
            ),
        ] {
            if on {
                let a = root(&p, a);
                let z = root(&p, z);
                if a == z {
                    return None;
                }
                p[a] = z as u8
            }
        }
    }
    let roots: Part = std::array::from_fn(|i| root(&p, H + i) as u8);
    Some(std::array::from_fn(|i| {
        roots.iter().position(|&z| z == roots[i]).unwrap() as u8
    }))
}
fn phase(j: usize) -> usize {
    if cfg!(phase13) && (j == 10 || j == 96) {
        return if j == 10 { 23 } else { 24 };
    }
    if cfg!(phase13) && (j == 9 || j == 97) {
        return if j == 9 { 21 } else { 22 };
    }
    if (cfg!(eleven) || cfg!(phase13)) && (j == 8 || j == 98) {
        return if j == 8 { 19 } else { 20 };
    }
    if j < 8 {
        j
    } else if j >= 99 {
        j - 88
    } else {
        8 + (j - 8) % 3
    }
}
fn spread(c: u16) -> usize {
    ((c & 1) + ((c & 2) << 2) + ((c & 4) << 4)) as usize
}
fn main() {
    let mut text = String::new();
    io::stdin().read_to_string(&mut text).unwrap();
    let prices: Vec<i64> = text
        .split_whitespace()
        .map(|x| x.parse().unwrap())
        .collect();
    assert_eq!(prices.len(), P * (H - 2) * 512);
    const INF: i64 = 1 << 60;
    assert!(prices
        .iter()
        .all(|x| x.unsigned_abs() < (INF / 2000) as u64));
    let eps = std::env::args().nth(1).map(|x| x.parse::<i64>().unwrap());
    let start: State = (0, 0, std::array::from_fn(|i| i as u8));
    let mut st = vec![start];
    let mut ids = HashMap::from([(start, 0)]);
    let mut memo = HashMap::new();
    let mut dest = Vec::<u32>::new();
    let mut off = vec![0];
    let mut i = 0;
    while i < st.len() {
        let (_, b, p) = st[i];
        for &(c, part) in memo
            .entry((b, p))
            .or_insert_with(|| {
                (0..1 << H)
                    .filter_map(|c| advance(b, p, c).map(|q| (c, q)))
                    .collect::<Vec<_>>()
            })
            .iter()
        {
            let k = *ids.entry((b, c, part)).or_insert_with(|| {
                st.push((b, c, part));
                (st.len() - 1) as u32
            });
            dest.push(k)
        }
        off.push(dest.len());
        i += 1;
    }
    drop(memo);
    drop(ids);
    let lut: Vec<Vec<i64>> = (0..P)
        .map(|h| {
            (0usize..3 * 32768)
                .map(|x| {
                    let r = 3 * (x >> 15);
                    let a = x as u16 & 31;
                    let b = (x >> 5) as u16 & 31;
                    let c = (x >> 10) as u16 & 31;
                    (0..3)
                        .filter(|&i| r + i < H - 2)
                        .map(|i| {
                            prices[(h * (H - 2) + r + i) * 512
                                + spread(a >> i)
                                + 2 * spread(b >> i)
                                + 4 * spread(c >> i)]
                        })
                        .sum()
                })
                .collect()
        })
        .collect();
    let weights = |h: usize| -> Vec<i64> {
        let mut ws = vec![0; dest.len()];
        let t = &lut[h];
        for (i, &(a, b, _)) in st.iter().enumerate() {
            let ab = |r: usize| ((a as usize >> r) & 31) + 32 * ((b as usize >> r) & 31);
            let (u, v, w) = (ab(0), 32768 + ab(3), 65536 + ab(6));
            for k in off[i]..off[i + 1] {
                let c = st[dest[k] as usize].1 as usize;
                ws[k] = t[u + 1024 * (c & 31)]
                    + t[v + 1024 * ((c >> 3) & 31)]
                    + t[w + 1024 * ((c >> 6) & 31)];
            }
        }
        ws
    };
    let bulk: Vec<_> = (8..11).map(weights).collect();
    if cfg!(uniform) {
        // Price the left end once. Three additional columns always
        // insert precisely the same phase cycle before the right end.
        let update=|v:&Vec<i64>,ws:&Vec<i64>|{
            let mut z=vec![INF;st.len()];
            for i in 0..st.len(){if v[i]!=INF{for k in off[i]..off[i+1]{
                let d=dest[k]as usize;z[d]=z[d].min(v[i]+ws[k])
            }}}
            z
        };
        let mut v=vec![INF;st.len()];v[0]=0;
        let end=if H==11 {98}else{99};
        for j in 0usize..end+2{
            v=update(&v,&if j<2{vec![0;dest.len()]}else{weights(phase(j-2))})
        }
        let mut z=v.clone();
        let period=std::env::var("STRIP_PERIOD").ok().and_then(|x|x.parse::<usize>().ok()).unwrap_or(1);
        assert!((1..=100).contains(&period));
        for j in end..end+3*period{z=update(&z,&bulk[(j-8)%3])}
        assert!(v.iter().chain(&z).all(|&a|a!=INF));
        let delta=z.iter().zip(&v).map(|(a,b)|a-b).min().unwrap();
        for j in end..107{v=update(&v,&weights(phase(j)))}
        println!("{} {delta} {}",v.iter().min().unwrap(),st.len());return
    }
    let mut fw = vec![vec![INF; st.len()]];
    fw[0][0] = 0;
    let mut count = 0u64;
    for j in 0usize..109 {
        let v = fw.last().unwrap();
        let mut next = vec![INF; st.len()];
        let h = phase(j.saturating_sub(2usize));
        let tmp;
        let ws = if (8..11).contains(&h) {
            &bulk[h - 8]
        } else {
            tmp = weights(h);
            &tmp
        };
        for (i, &z) in v.iter().enumerate() {
            if z == INF {
                continue;
            }
            for k in off[i]..off[i + 1] {
                let d = dest[k] as usize;
                let w = if j < 2 { 0 } else { ws[k] };
                next[d] = next[d].min(z + w);
                count += 1
            }
        }
        fw.push(next);
    }
    let best = *fw[109].iter().min().unwrap();
    let mut out = BufWriter::new(io::stdout());
    writeln!(out, "{best} {count}").unwrap();
    if let Some(eps) = eps {
        let sampled = std::env::args().nth(2).is_some();
        let mut bw_hist = Vec::new();
        let mut bw = vec![0; st.len()];
        for j in (0usize..109).rev() {
            let h = phase(j.saturating_sub(2));
            let tmp;
            let ws = if (8..11).contains(&h) {
                &bulk[h - 8]
            } else {
                tmp = weights(h);
                &tmp
            };
            let mut next = vec![INF; st.len()];
            for (i, &(a, b, p)) in st.iter().enumerate() {
                if fw[j][i] == INF {
                    continue;
                }
                for k in off[i]..off[i + 1] {
                    let d = dest[k] as usize;
                    let v = bw[d] + if j < 2 { 0 } else { ws[k] };
                    next[i] = next[i].min(v);
                    if !sampled && fw[j][i] + v <= best + eps {
                        let bits = p.iter().rev().fold(0u64, |s, &z| 16 * s + z as u64);
                        writeln!(out, "{j} {a} {b} {bits} {}", st[d].1).unwrap();
                    }
                }
            }
            if sampled {
                bw_hist.push(bw)
            }
            bw = next;
        }
        assert_eq!(bw[0], best);
        if sampled {
            let mut active = HashSet::new();
            let mut rng = 71113u64;
            for iter in 0..240 {
                let mut i = 0;
                let mut spent = 0;
                for j in 0usize..109 {
                    let h = phase(j.saturating_sub(2));
                    let mut options = Vec::new();
                    for k in off[i]..off[i + 1] {
                        let d = dest[k] as usize;
                        let (a, b, _) = st[i];
                        let c = st[d].1;
                        let w: i64 = if j < 2 {
                            0
                        } else {
                            (0..H - 2)
                                .map(|r| {
                                    prices[(h * (H - 2) + r) * 512
                                        + spread(a >> r)
                                        + 2 * spread(b >> r)
                                        + 4 * spread(c >> r)]
                                })
                                .sum()
                        };
                        if spent + w + bw_hist[108 - j][d] <= best + if iter == 0 { 0 } else { eps }
                        {
                            options.push((d, w));
                        }
                    }
                    rng ^= rng << 13;
                    rng ^= rng >> 7;
                    rng ^= rng << 17;
                    let (d, w) = options[(rng as usize) % options.len()];
                    spent += w;
                    active.insert((j, i, st[d].1));
                    i = d;
                }
            }
            let mut a: Vec<_> = active.into_iter().collect();
            a.sort_unstable();
            for (j, i, c) in a {
                let (a, b, p) = st[i];
                let bits = p.iter().rev().fold(0u64, |s, &z| 16 * s + z as u64);
                writeln!(out, "{j} {a} {b} {bits} {c}").unwrap();
            }
        }
    }
}
