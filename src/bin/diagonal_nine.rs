//! Meet across one primal normal slice; distances on either side never exceed 1.
use std::collections::{HashMap, VecDeque};
use std::io::{self, Read};
const ALL: u32 = (1 << 18) - 1;
const EVEN: u32 = ALL / 3;
fn right(x: u32) -> u32 {
    x >> 1 | (x & 1) << 17
}
fn left(x: u32) -> u32 {
    (x << 1) & ALL | x >> 17
}
fn cost(prev: u32, next: u32) -> u8 {
    let (a, b, c, d) = (prev, right(prev), next, left(next));
    let (s, t) = (a ^ b, c ^ d);
    let two = (a & b) ^ (c & d) ^ (s & t);
    ((two & !(s ^ t) & EVEN).count_ones() + 2 * (two & (s ^ t) & EVEN).count_ones()) as u8
}
fn partial_cost(prev:u32,v:u32,occ:u32)->u8 {
    let lo=(v^(ALL^EVEN))&occ;
    let hi=lo|(ALL^occ);
    let a=prev;
    let b=right(prev);
    let c=lo;
    let d=left(lo);
    let possible_full=a&b&hi&left(hi);
    let two=(a&b)|(c&d)|((a|b)&(c|d));
    let three=(a&b&(c|d))|(c&d&(a|b));
    (((two&!possible_full&EVEN).count_ones())+((three&!possible_full&EVEN).count_ones())) as u8
}
type State = (u32, u32, u8); // occupied on even slice, previous midpoint mask, primal phase
type Index = HashMap<(u32, u8), Vec<(u32, u8)>>;
fn flip(x: u32) -> u32 {
    (x & 1) | ((x.reverse_bits() >> 13) & (ALL ^ 1))
}
fn main() {
    let wide = std::env::args().any(|arg| arg == "--sector");
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap();
    let mut need = [false; 19];
    for line in input.lines() {
        let s: u32 = line.split_whitespace().next().unwrap().parse().unwrap();
        let n = s.count_ones() as usize;
        need[n] = true;
        need[18 - n] = true;
    }
    // Only balanced (nine incoming) masks are reached.
    let mut trans = vec![Vec::new(); (ALL + 1) as usize];
    for occ in 0..=ALL {
        if !need[occ.count_ones() as usize] {
            continue;
        }
        if occ.count_ones() != 9 && !(wide && (6..=12).contains(&occ.count_ones())) {
            continue;
        }
        let free = ALL ^ occ;
        let mut v = free;
        loop {
            let h = right(free ^ v);
            if v & h == 0 {
                trans[occ as usize].push((v, v | h))
            }
            if v == 0 {
                break;
            }
            v = (v - 1) & free;
        }
    }
    let mut tables: HashMap<(State, u8, bool), Index> = HashMap::new();
    for line in input.lines() {
        let ns: Vec<u32> = line
            .split_whitespace()
            .map(|w| w.parse().unwrap())
            .collect();
        let budget = ns[4] as u8;
        assert!(
            (wide
                && budget <= 6
                && (6..=12).contains(&ns[0].count_ones())
                && ns[0].count_ones() + ns[2].count_ones() == 18)
                || (budget <= 3 && ns[0].count_ones() == 9 && ns[2].count_ones() == 9)
        );
        let half = budget / 2;
        // For budget 2 both halves 1 suffice; for budget 3 use 1+one step+1.
        let rad = if wide { half } else { half.min(1) };
        let keys = [
            (
                (ns[0], ns[1], 0),
                if wide {
                    budget.saturating_sub(1) / 2
                } else {
                    rad
                },
                false,
            ),
            ((ns[2], ns[3], 0), rad, true),
        ];
        for &(start, r, rev) in &keys {
            if tables.contains_key(&(start, r, rev)) {
                continue;
            }
            let mut dist = HashMap::from([(start, 0u8)]);
            let mut q = VecDeque::from([(start, 0u8)]);
            while let Some(((occ, prev, phase), paid)) = q.pop_front() {
                if dist[&(occ, prev, phase)] != paid {
                    continue;
                }
                for &(v, o) in &trans[occ as usize] {
                    if paid+partial_cost(prev,v,o)>r {continue}
                    for &(w, end) in &trans[o as usize] {
                        let mid = (v | w) ^ (ALL ^ EVEN);
                        let nk = paid + cost(prev, mid);
                        if nk > r {
                            continue;
                        }
                        let st = (end, mid, (phase + 1) % 9);
                        if dist.get(&st).is_none_or(|&old| nk < old) {
                            dist.insert(st, nk);
                            q.push_back((st, nk));
                        }
                    }
                }
            }
            let mut index = Index::new();
            for ((occ, mid, ph), k) in dist {
                let (m, p, s) = if rev {
                    (ALL ^ flip(occ), (9 - ph) % 9, flip(mid))
                } else {
                    (occ, ph, mid)
                };
                index.entry((m, p)).or_default().push((s, k));
            }
            tables.insert((start, r, rev), index);
        }
        let low = &tables[&keys[0]];
        let high = &tables[&keys[1]];
        let mut best = 255;
        let rotation=ns.get(7).copied().unwrap_or(0);
        let offset=ns.get(8).copied().unwrap_or(0) as u8;
        let rotate=|x:u32| ((x<<rotation)&ALL)|(x>>(18-rotation));
        for (key, ls) in low {
            if let Some(rs) = high.get(&(rotate(key.0),(key.1+offset)%9)) {
                for &(p, k) in ls {
                    for &(n, j) in rs {
                        best = best.min(k + j + cost(rotate(p), n));
                    }
                }
            }
        }
        println!("{} {} {}", ns[5], ns[6], best);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn reversal_and_scalar_star_cost() {
        for i in 0..18 {
            assert_eq!(flip(1 << i), 1 << ((18 - i) % 18));
        }
        for i in (0..18).step_by(2) {
            for bits in 0u32..16 {
                let p = ((bits & 1) << i) | (((bits >> 1) & 1) << ((i + 1) % 18));
                let n = (((bits >> 2) & 1) << i) | (((bits >> 3) & 1) << ((i + 17) % 18));
                let d = bits.count_ones();
                assert_eq!(cost(p, n), if d == 2 || d == 3 { (d - 1) as u8 } else { 0 });
                assert_eq!(cost(p, n), cost(flip(n), flip(p)));
                for mask in 0u32..4 {
                    let occ=((mask&1)<<i)|(((mask>>1)&1)<<((i+17)%18));
                    let v=occ&(n^(ALL^EVEN));
                    assert!(partial_cost(p,v,occ)<=cost(p,n));
                }
            }
        }
    }
}
