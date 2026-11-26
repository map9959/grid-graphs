//! All-width threshold queries on the (6,12) doubled cylinder.
use std::collections::{HashMap, VecDeque};
use std::io::{self, Read};

fn pack(v: u64, h: u64, l: u64, hist: u64, z: u64) -> u64 {
    v | (h << 6) | (l << 12) | (hist << 18) | (z << 30)
}
fn three(x: u64, phase: u64) -> u64 {
    let y = x >> (1 - (phase & 1));
    (y & 1) | ((y >> 1) & 2) | ((y >> 2) & 4)
}
fn main() {
    let mut text = String::new();
    io::stdin().read_to_string(&mut text).unwrap();
    for line in text.lines() {
        let ns: Vec<u64> = line
            .split_whitespace()
            .map(|x| x.parse().unwrap())
            .collect();
        let limit = ns[0] as u8;
        let state = |p: usize| pack(ns[p], ns[p + 1], ns[p + 2], ns[p + 3], 0);
        let start = state(1);
        let mut dist = HashMap::from([(start, 0u8)]);
        let mut q = VecDeque::from([(start, 0u8)]);
        while let Some((s, cost)) = q.pop_front() {
            if cost != dist[&s] {
                continue;
            }
            let v = s & 63;
            let l = (s >> 12) & 63;
            let free = 63 ^ ((s | (s >> 6)) & 63);
            let z = s >> 30;
            let hist = (s >> 18) & 4095;
            let mut up = free;
            loop {
                let across = free ^ up;
                if across & l == 0 {
                    let m = three(up | v, z);
                    let mut loss = 0;
                    if z % 2 == 0 {
                        let past = hist & 7;
                        let old_h = 7 ^ ((hist >> 3) & 7);
                        let new_h = 7 ^ ((hist >> 9) & 7);
                        for i in 0..3 {
                            let deg = ((past >> ((i + 2) % 3)) & 1)
                                + ((m >> i) & 1)
                                + ((old_h >> i) & 1)
                                + ((new_h >> i) & 1);
                            debug_assert!(deg > 0);
                            if deg < 4 {
                                loss += (deg - 1) as u8;
                            }
                        }
                    }
                    let nk = cost + loss;
                    if nk <= limit {
                        let t = pack(
                            l,
                            across,
                            ((up << 1) & 63) | (up >> 5),
                            (hist >> 3) | (m << 9),
                            (z + 1) % 12,
                        );
                        if dist.get(&t).is_none_or(|&old| nk < old) {
                            dist.insert(t, nk);
                            if loss == 0 {
                                q.push_front((t, nk))
                            } else {
                                q.push_back((t, nk))
                            }
                        }
                    }
                }
                if up == 0 {
                    break;
                }
                up = (up - 1) & free;
            }
            assert!(dist.len() < 5_000_000, "state guard exceeded; inconclusive");
        }
        print!("{}", dist.len());
        for p in (5..ns.len()).step_by(4) {
            print!(" {}", dist.get(&state(p)).copied().unwrap_or(255));
        }
        println!();
    }
}
