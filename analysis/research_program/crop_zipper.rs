//! Delete one row/column from a zipper, repair and complete the marked forest.
use std::io::{self, Read};
fn root(p: &mut [usize], mut x: usize) -> usize {
    while p[x] != x {
        p[x] = p[p[x]];
        x = p[x]
    }
    x
}
fn take(x: usize, marked: &[bool], nbr: &[Vec<usize>], p: &mut [usize]) -> bool {
    let mut seen = [usize::MAX; 5];
    let mut k = 1;
    seen[0] = root(p, x);
    for &v in &nbr[x] {
        if !marked[v] {
            let z = root(p, v);
            if seen[..k].contains(&z) {
                return false;
            }
            seen[k] = z;
            k += 1;
        }
    }
    for i in 1..k {
        p[seen[i]] = seen[0]
    }
    true
}
fn main() {
    let mut txt = String::new();
    io::stdin().read_to_string(&mut txt).unwrap();
    let rows: Vec<_> = txt.lines().collect();
    let n = rows.len() - 1;
    assert!(rows.iter().all(|r| r.len() == n + 1));
    let base = rows
        .iter()
        .flat_map(|r| r.bytes().map(|b| b == b'#'))
        .collect::<Vec<_>>();
    let nbr = (0..n * n)
        .map(|x| {
            let mut v = Vec::new();
            if x >= n {
                v.push(x - n)
            }
            if x + n < n * n {
                v.push(x + n)
            }
            if x % n > 0 {
                v.push(x - 1)
            }
            if x % n + 1 < n {
                v.push(x + 1)
            }
            v
        })
        .collect::<Vec<_>>();
    let total = base.iter().filter(|&&x| x).count();
    let mut seams = Vec::new();
    for i in 0..=n {
        for j in 0..=n {
            let loss = base[i * (n + 1)..(i + 1) * (n + 1)]
                .iter()
                .filter(|&&z| z)
                .count()
                + (0..=n).filter(|&r| r != i && base[r * (n + 1) + j]).count();
            seams.push((loss, i, j))
        }
    }
    seams.sort_unstable();
    let k = (n - 1) / 3;
    let threshold = 3 * k * k + 5 * k + (3 * k - 13) / 10;
    let mut best = 0;
    for (loss, i, j) in seams {
        if total - loss + 12 < threshold {
            break;
        }
        let mut m = vec![false; n * n];
        let mut p = (0..n * n).collect::<Vec<_>>();
        let mut bands: [Vec<usize>; 4] = std::array::from_fn(|_| vec![]);
        let mut rest = Vec::new();
        for x in 0..n * n {
            let r = x / n;
            let c = x % n;
            let d = r.abs_diff(i).min(c.abs_diff(j)).min(3);
            if base[(r + usize::from(r >= i)) * (n + 1) + c + usize::from(c >= j)] {
                bands[d].push(x)
            } else if d <= 2 {
                rest.push(x)
            }
        }
        let mut score = 0;
        for x in bands.iter().rev().flatten().chain(&rest).copied() {
            if take(x, &m, &nbr, &mut p) {
                m[x] = true;
                score += 1
            }
        }
        if score > best {
            best = score;
            if score > threshold {
                println!("side {n} seam {i},{j} verified candidate {score}");
                for r in m.chunks(n) {
                    println!(
                        "{}",
                        r.iter()
                            .map(|&b| if b { '#' } else { '.' })
                            .collect::<String>()
                    )
                }
            }
        }
    }
    println!("side {n} largest repaired score {best}, comb {threshold}")
}
