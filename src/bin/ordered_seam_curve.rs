//! Exact min-plus histograms. The input is a layered seam automaton; no
//! counter cap. At layer j at most j physical tile rows have been read.
use std::io::{self, Read};

fn main() {
    let mut s = String::new();
    io::stdin().read_to_string(&mut s).unwrap();
    let mut it = s.split_whitespace().map(|x| x.parse::<usize>().unwrap());
    let k = it.next().unwrap();
    let inf = u32::MAX / 2;
    // Three independent histograms: all hops, skips, constant-symbol packets.
    let mut old = vec![inf; 3 * (k + 1)];
    for t in 0..3 {
        old[t * (k + 1)] = 0;
    }
    for j in 0..k {
        let n = it.next().unwrap();
        let e = it.next().unwrap();
        let mut new = vec![inf; n * 3 * (k + 1)];
        for _ in 0..e {
            let a = it.next().unwrap();
            let b = it.next().unwrap();
            let cost = it.next().unwrap() as u32;
            let flags = it.next().unwrap();
            for t in 0..3 {
                let from = (a * 3 + t) * (k + 1);
                let to = (b * 3 + t) * (k + 1) + ((flags >> t) & 1);
                for (x, y) in old[from..=from + j].iter().zip(&mut new[to..=to + j]) {
                    *y = (*y).min(x + cost);
                }
            }
        }
        old = new;
    }
    assert!(it.next().is_none());
    for t in 0..3 {
        for n in 0..=k {
            let v = old
                .chunks(3 * (k + 1))
                .map(|a| a[t * (k + 1) + n])
                .min()
                .unwrap_or(inf);
            print!("{} ", if v == inf { -1 } else { i64::from(v) });
        }
        println!();
    }
}
