//! Reach a free physical boundary from a saturated background at arbitrary depth.
use std::collections::{HashMap, VecDeque};
use std::io::{self, Read};
const EVEN: u32 = 0x55555555;
fn right<const W: u32>(x: u32) -> u32 {
    x >> 1 | (x & 1) << (W - 1)
}
fn left<const W: u32>(x: u32) -> u32 {
    ((x << 1) & ((1 << W) - 1)) | x >> (W - 1)
}

// All cyclic row matches with the specified incoming sites. The other
// sites either point forward or pair with a horizontal neighbor.
fn dfs<const W: u32>(free: u32, out: u32, rows: &mut Vec<u32>) {
    if free == 0 {
        rows.push(out);
        return;
    }
    let bit = free & free.wrapping_neg();
    dfs::<W>(free ^ bit, out | bit, rows);
    for adj in [left::<W>(bit), right::<W>(bit)] {
        if adj & free != 0 {
            dfs::<W>(free ^ bit ^ adj, out, rows);
        }
    }
}
fn choices<const W: u32>(cache: &mut HashMap<u32, Vec<u32>>, occ: u32) -> &Vec<u32> {
    cache.entry(occ).or_insert_with(|| {
        let mut v = Vec::new();
        dfs::<W>(((1 << W) - 1) ^ occ, 0, &mut v);
        v.sort_unstable();
        v.dedup();
        v
    })
}
fn local(a: u32, b: u32, c: u32, d: u32, boundary: bool) -> u8 {
    let (s, t) = (a ^ b, c ^ d);
    let two = (a & b) ^ (c & d) ^ (s & t);
    if boundary {
        let full = a & b & c;
        // For a degree-three boundary site, loss zero if full;
        // otherwise it is its degree (degree-1 incoming + deficiency).
        return ([a, b, c]
            .iter()
            .map(|m| (m & EVEN & !full).count_ones())
            .sum::<u32>()) as u8;
    }
    ((two & !(s ^ t) & EVEN).count_ones() + 2 * (two & (s ^ t) & EVEN).count_ones()) as u8
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn row_matchings_and_vertex_account() {
        let mut cache = HashMap::new();
        // Only the two adjacent sites across the periodic cut are free.
        assert_eq!(
            *choices::<18>(&mut cache, ((1 << 18) - 1) ^ ((1 << 17) | 1)),
            vec![0, (1 << 17) | 1]
        );
        for col in (0..18).step_by(2) {
            for bits in 0u32..16 {
                let [a, b, c, d] = [0, 1, 2, 3].map(|i| ((bits >> i) & 1) << col);
                let deg = bits.count_ones();
                assert_eq!(
                    local(a, b, c, d, false),
                    if (2..4).contains(&deg) {
                        (deg - 1) as u8
                    } else {
                        0
                    }
                );
                let bdeg = (bits & 7).count_ones();
                assert_eq!(
                    local(a, b, c, 0, true),
                    if bdeg == 3 { 0 } else { bdeg as u8 }
                );
            }
        }
    }
}
fn main() {
    if std::env::args().any(|s| s == "--six") {
        run::<12>()
    } else {
        run::<18>()
    }
}
fn run<const W: u32>() {
    let mut text = String::new();
    io::stdin().read_to_string(&mut text).unwrap();
    let mut evens = HashMap::new();
    let mut odds = HashMap::new();
    for line in text.lines() {
        let n: Vec<u32> = line
            .split_whitespace()
            .map(|s| s.parse().unwrap())
            .collect();
        let limit = n[2] as u8;
        let start = (n[0], n[1] & EVEN, 0u8);
        let mut q = VecDeque::from([(start, 0u8)]);
        let mut dist = HashMap::from([(start, 0u8)]);
        let mut best = limit + 1;
        while let Some(((incoming, prev, phase), paid)) = q.pop_front() {
            if paid >= best || dist[&(incoming, prev, phase)] != paid {
                continue;
            }
            for &out in choices::<W>(&mut evens, incoming) {
                let horiz = ((1 << W) - 1) ^ (out | incoming);
                let a = right::<W>(horiz);
                let b = left::<W>(horiz);
                let c = prev;
                if out == 0 && phase == 0 {
                    best = best.min(paid + local(a, b, c, 0, true));
                }
                // The occupancy on the next odd row guarantees some normal
                // edges, and others can only take one of two values. Minimize
                // the local cost independently for each possible degree.
                let both = a & b & c;
                let at_least_two = (a & b) | (a & c) | (b & c);
                let unavoidable = (at_least_two & !both) | ((a | b | c) & out & !both);
                if paid + (unavoidable & EVEN).count_ones() as u8 > limit {
                    continue;
                }
                for &next in choices::<W>(&mut odds, out) {
                    let mid = (out | next) & EVEN;
                    let cost = paid + local(a, b, c, mid, false);
                    let st = (next, mid, (phase + 1) % (W as u8 / 2));
                    if cost <= limit && cost < best && dist.get(&st).is_none_or(|&old| old > cost) {
                        dist.insert(st, cost);
                        q.push_back((st, cost))
                    }
                }
            }
        }
        println!("{} {} {}", n[3], best, dist.len());
    }
}
