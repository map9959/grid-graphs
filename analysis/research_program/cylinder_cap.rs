//! Repeat W columns across the square. The two end bars are the only
//! cycles allowed on the cylinder, in distinct components. The lift is
//! a forest, as is every finite crop. Score counts the actual crop.
use std::collections::HashMap;
type Key = (u16, u64);
fn rt(p: &mut [u8; 34], mut a: usize) -> usize {
    while p[a] as usize != a {
        p[a] = p[p[a] as usize];
        a = p[a] as usize
    }
    a
}
fn edge(p: &mut [u8; 34], a: usize, b: usize) -> bool {
    let x = rt(p, a);
    let y = rt(p, b);
    p[x] = y as u8;
    x != y
}
fn trans(w: usize, (old, key): Key, bar: bool) -> Vec<Key> {
    let full = (1u16 << w) - 1;
    let diag = ((old << 1) | (old >> (w - 1)) | (old >> 1) | ((old & 1) << (w - 1))) & full;
    let mut ans = Vec::new();
    let allow = full ^ diag;
    let mut m = if bar { full } else { allow };
    loop {
        if m & diag == 0 {
            let mut p = std::array::from_fn(|i| i as u8);
            for i in 0..=w {
                p[i] = ((key >> (4 * i)) & 15) as u8
            }
            let mut ok = true;
            let off = w + 1;
            for i in 0..w {
                let b = 1 << i;
                let j = (i + 1) % w;
                if (old | m) & b != 0 && !edge(&mut p, i, off + i) {
                    ok = false;
                    break;
                }
                if (!bar || j != 0) && m & (b | (1 << j)) != 0 && !edge(&mut p, off + i, off + j) {
                    ok = false;
                    break;
                }
            }
            if ok && (!bar || rt(&mut p, off) != rt(&mut p, w)) {
                let mut reps = [255; 34];
                let mut z = 0u64;
                for i in 0..=w {
                    let a = if i == w { w } else { off + i };
                    let r = rt(&mut p, a);
                    if reps[r] == 255 {
                        reps[r] = i as u8
                    }
                    z |= (reps[r] as u64) << (4 * i)
                }
                ans.push((m, z));
            }
        }
        if bar || m == 0 {
            break;
        }
        m = (m - 1) & allow;
    }
    ans
}
fn main() {
    let a: Vec<_> = std::env::args()
        .skip(1)
        .map(|s| s.parse::<usize>().unwrap())
        .collect();
    let (w, n) = (a[0], a[1]);
    assert!(w <= 15 && w >= 3 && n % 3 == 1);
    let full = (1u16 << w) - 1;
    let mut dp = HashMap::from([((full, 0), n)]);
    let mut cache = HashMap::new();
    let scores: Vec<_> = (0..=full)
        .map(|m| {
            m.count_ones() as usize * (n / w) + (m & ((1 << (n % w)) - 1)).count_ones() as usize
        })
        .collect();
    let mut hist = Vec::new();
    let keep = a.get(2).copied().unwrap_or(usize::MAX);
    for j in 1..n {
        let mut nd = HashMap::new();
        let mut pred = HashMap::new();
        for (&s, &v) in &dp {
            for &z in cache
                .entry((s, j == n - 1))
                .or_insert_with(|| trans(w, s, j == n - 1))
                .iter()
            {
                let q = v + scores[z.0 as usize];
                let e = nd.entry(z).or_insert(0);
                if q > *e {
                    *e = q;
                    pred.insert(z, s);
                }
            }
        }
        if nd.len() > keep {
            let mut opts: Vec<_> = nd.iter().map(|(&s, &v)| (usize::MAX - v, s)).collect();
            opts.select_nth_unstable(keep);
            opts.truncate(keep);
            nd = opts.into_iter().map(|(v, s)| (s, usize::MAX - v)).collect();
            pred.retain(|k, _| nd.contains_key(k));
        }
        hist.push(pred);
        dp = nd;
    }
    let (&mut_key, &score) = dp.iter().max_by_key(|(s, v)| (**v, **s)).unwrap();
    let mut s = mut_key;
    let k = n / 3;
    println!(
        "width {w} side {n} score {score} comb {} cache {}",
        3 * k * k + 5 * k + (3 * k - 13) / 10,
        cache.len()
    );
    let mut rows = vec![s.0];
    for pr in hist.iter().rev() {
        s = pr[&s];
        rows.push(s.0)
    }
    for &m in rows.iter().rev() {
        println!(
            "{}",
            (0..n)
                .map(|i| if m & (1 << (i % w)) != 0 { '#' } else { '.' })
                .collect::<String>()
        )
    }
}
