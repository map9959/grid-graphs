//! Exhaust the period-12 diagonal cylinder at bounded incoming-to-U cost.
use std::collections::{HashMap, VecDeque};
use std::io::{self, Read};

const ALL: u16 = 4095;
const EVEN: u16 = 0x555;
fn right(x: u16) -> u16 {
    (x >> 1) | ((x & 1) << 11)
}
fn left(x: u16) -> u16 {
    ((x << 1) & ALL) | (x >> 11)
}

#[derive(Clone, Copy, Eq, Hash, PartialEq)]
struct State {
    occ: u16,
    vert: u16,
    prev: u16,
    phase: u8,
}

// One even->odd->even step. Degree at each of six primal sites is
// the sum of four local bits. Since one incident edge points out,
// incoming-to-U cost is 1 at degree 2, 2 at degree 3, zero otherwise.
fn cost(prev: u16, next: u16) -> u8 {
    let (a, b, c, d) = (prev, right(prev), next, left(next));
    let (s, t) = (a ^ b, c ^ d);
    let two = (a & b) ^ (c & d) ^ (s & t);
    ((two & !(s ^ t) & EVEN).count_ones() + 2 * (two & (s ^ t) & EVEN).count_ones()) as u8
}
fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut trans = vec![Vec::new(); 4096];
    for occ in 0..=ALL {
        let free = ALL ^ occ;
        let mut v = free;
        loop {
            let h = right(free ^ v);
            if v & h == 0 {
                trans[occ as usize].push((v, v | h));
            }
            if v == 0 {
                break;
            }
            v = (v - 1) & free;
        }
    }
    for line in input.lines() {
        let n: Vec<u16> = line
            .split_whitespace()
            .map(|s| s.parse().unwrap())
            .collect();
        let start = State {
            occ: n[0],
            vert: n[1],
            prev: n[2],
            phase: 0,
        };
        let budget = n[3] as u8;
        let mut dist = HashMap::from([(start, 0u8)]);
        let mut q = VecDeque::from([(start, 0u8)]);
        while let Some((s, k)) = q.pop_front() {
            if dist[&s] != k {
                continue;
            }
            for &(v, occ) in &trans[s.occ as usize] {
                for &(w, end) in &trans[occ as usize] {
                    let mid = (v | w) ^ 0xaaa;
                    let nk = k + cost(s.prev, mid);
                    if nk > budget {
                        continue;
                    }
                    let next = State {
                        occ: end,
                        vert: w,
                        prev: mid,
                        phase: (s.phase + 1) % 6,
                    };
                    if dist.get(&next).is_none_or(|&old| nk < old) {
                        dist.insert(next, nk);
                        if nk == k {
                            q.push_front((next, nk))
                        } else {
                            q.push_back((next, nk))
                        }
                    }
                }
            }
        }
        print!("{}", dist.len());
        for x in n[4..].chunks_exact(3) {
            let end = State {
                occ: x[0],
                vert: x[1],
                prev: x[2],
                phase: 1,
            };
            print!(" {}", dist.get(&end).copied().unwrap_or(255));
        }
        println!();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn four_incident_edges_have_correct_cost_at_every_column() {
        for c in (0..12).step_by(2) {
            for bits in 0u16..16 {
                let prev = ((bits & 1) << c) | (((bits >> 1) & 1) << ((c + 1) % 12));
                let next = (((bits >> 2) & 1) << c) | (((bits >> 3) & 1) << ((c + 11) % 12));
                let n = bits.count_ones();
                assert_eq!(
                    cost(prev, next),
                    if n == 2 || n == 3 { (n - 1) as u8 } else { 0 }
                );
            }
        }
    }
}
