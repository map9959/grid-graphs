//! Forests on the infinite horizontal cover of a width-W cylinder.
//! A quotient component may be unicyclic if its cycle winds oddly.
use std::collections::HashMap;
use std::hash::Hash;
#[derive(Copy, Clone, Hash, Ord, PartialOrd, Eq, PartialEq)]
struct S {
    m: u16,
    p: u64,
    flip: u16,
    cyc: u16,
}
fn root(p: &[u8; 32], w: &[bool; 32], mut i: usize) -> (usize, bool) {
    let mut z = false;
    while p[i] as usize != i {
        z ^= w[i];
        i = p[i] as usize
    }
    (i, z)
}
fn edge(
    p: &mut [u8; 32],
    w: &mut [bool; 32],
    sat: &mut [bool; 32],
    a: usize,
    b: usize,
    odd: bool,
) -> bool {
    let (x, s) = root(p, w, a);
    let (y, t) = root(p, w, b);
    let f = s ^ t ^ odd;
    if x == y {
        if sat[x] || !f {
            return false;
        }
        sat[x] = true;
        return true;
    }
    if sat[x] && sat[y] {
        return false;
    }
    p[x] = y as u8;
    w[x] = f;
    sat[y] |= sat[x];
    true
}
fn trans(n: usize, s: S, first: bool) -> Vec<S> {
    let full = (1u16 << n) - 1;
    let diag = ((s.m << 1) | (s.m >> (n - 1)) | (s.m >> 1) | ((s.m & 1) << (n - 1))) & full;
    let allow = full ^ diag;
    let mut ans = vec![];
    let mut m = allow;
    loop {
        let mut p = std::array::from_fn(|i| i as u8);
        let mut f = [false; 32];
        let mut sat = [false; 32];
        for i in 0..n {
            p[i] = ((s.p >> (4 * i)) & 15) as u8;
            f[i] = s.flip & (1 << i) != 0;
            sat[i] = s.cyc & (1 << i) != 0
        }
        let mut ok = true;
        for i in 0..n {
            let j = (i + 1) % n;
            if !first
                && (s.m | m) & (1 << i) != 0
                && !edge(&mut p, &mut f, &mut sat, i, n + i, false)
            {
                ok = false;
                break;
            }
            if m & ((1 << i) | (1 << j)) != 0
                && !edge(&mut p, &mut f, &mut sat, n + i, n + j, j == 0)
            {
                ok = false;
                break;
            }
        }
        if ok {
            let mut z = S {
                m,
                p: 0,
                flip: 0,
                cyc: 0,
            };
            let mut rep = [255; 32];
            let mut ofs = [false; 32];
            for i in 0..n {
                let (r, g) = root(&p, &f, n + i);
                if rep[r] == 255 {
                    rep[r] = i as u8;
                    ofs[r] = g;
                    if sat[r] {
                        z.cyc |= 1 << i
                    }
                }
                z.p |= (rep[r] as u64) << (4 * i);
                if !sat[r] && g != ofs[r] {
                    z.flip |= 1 << i
                }
            }
            ans.push(z)
        }
        if m == 0 {
            break;
        }
        m = (m - 1) & allow
    }
    ans
}
fn main() {
    let a: Vec<_> = std::env::args()
        .skip(1)
        .map(|s| s.parse::<usize>().unwrap())
        .collect();
    let (w, n) = (a[0], a[1]);
    let keep = a.get(2).copied().unwrap_or(usize::MAX);
    assert!(w >= 3 && w <= 15 && n >= 16);
    let score: Vec<_> = (0u16..1 << w)
        .map(|m| {
            m.count_ones() as usize * (n / w) + (m & ((1 << (n % w)) - 1)).count_ones() as usize
        })
        .collect();
    let start = S {
        m: 0,
        p: (0..w).map(|i| (i as u64) << (4 * i)).sum(),
        cyc: 0,
        flip: 0,
    };
    let mut dp = HashMap::from([(start, 0)]);
    let mut cache = HashMap::new();
    let mut hist = Vec::new();
    for j in 0..n {
        let mut nd = HashMap::new();
        let mut pred = HashMap::new();
        for (&s, &v) in &dp {
            for &z in cache
                .entry((s, j == 0))
                .or_insert_with(|| trans(w, s, j == 0))
                .iter()
            {
                let a = v + score[z.m as usize];
                if nd.get(&z).map_or(true, |&q| q < a) {
                    nd.insert(z, a);
                    pred.insert(z, s);
                }
            }
        }
        if nd.len() > keep {
            let mut v: Vec<_> = nd.iter().map(|(&s, &v)| (usize::MAX - v, s)).collect();
            v.select_nth_unstable(keep);
            v.truncate(keep);
            nd = v.into_iter().map(|(v, s)| (s, usize::MAX - v)).collect();
            pred.retain(|s, _| nd.contains_key(s));
        }
        hist.push(pred);
        dp = nd;
    }
    let (&last, &v) = dp.iter().max_by_key(|(s, v)| (**v, **s)).unwrap();
    let k = n / 3;
    println!(
        "side {n} period {w} score {v} comb {} states {}",
        3 * k * k + 5 * k + (3 * k - 13) / 10,
        dp.len()
    );
    let mut rows = Vec::new();
    let mut s = last;
    for h in hist.iter().rev() {
        rows.push(s.m);
        s = h[&s]
    }
    for m in rows.iter().rev() {
        println!(
            "{}",
            (0..n)
                .map(|i| if m & (1 << (i % w)) != 0 { '#' } else { '.' })
                .collect::<String>()
        )
    }
}
