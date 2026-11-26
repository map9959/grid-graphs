//! Exact primal forest transfer on a diagonal cylinder, with signed winding.
use fxhash::FxHashMap as Map;
use std::io::Write;

#[derive(Clone)]
struct Uf {
    p: [u8; 32],
    h: [i16; 32],
    w: [i16; 32],
}
impl Uf {
    fn new() -> Self {
        Self {
            p: std::array::from_fn(|i| i as u8),
            h: [0; 32],
            w: [0; 32],
        }
    }
    fn root(&self, mut i: usize) -> (usize, i16) {
        let mut h = 0;
        while self.p[i] as usize != i {
            h += self.h[i];
            i = self.p[i] as usize
        }
        (i, h)
    }
    fn link(&mut self, i: usize, j: usize, x: i16) -> bool {
        let (a, h) = self.root(i);
        let (b, k) = self.root(j);
        let v = h + x - k;
        if a == b {
            if self.w[a] != 0 || v == 0 {
                return false;
            }
            self.w[a] = v.abs()
        } else {
            if self.w[a] != 0 && self.w[b] != 0 {
                return false;
            }
            self.p[b] = a as u8;
            self.h[b] = v;
            self.w[a] |= self.w[b]
        }
        true
    }
    fn sig(&self, sites: &[usize]) -> Sig {
        let mut rep = [255u8; 32];
        let mut off = [0i16; 32];
        let mut s = Sig([0; 9]);
        for (i, &v) in sites.iter().enumerate() {
            let (a, h) = self.root(v);
            if rep[a] == 255 {
                rep[a] = i as u8;
                off[a] = h
            }
            let w = self.w[a];
            let x = h - off[a];
            let x = if w != 0 { x.rem_euclid(w) } else { x };
            assert!((-64..64).contains(&x) && w < 32);
            s.0[i] = rep[a] as u16 | (((x + 64) as u16) << 4) | ((w as u16) << 11);
        }
        s
    }
    fn load(&mut self, s: Sig, sites: &[usize]) -> bool {
        for (i, &site) in sites.iter().enumerate() {
            let e = s.0[i];
            let r = (e & 15) as usize;
            if i != r && !self.link(sites[r], site, ((e >> 4) & 127) as i16 - 64) {
                return false;
            }
        }
        for (i, &site) in sites.iter().enumerate() {
            let e = s.0[i];
            if e >> 11 != 0 && e & 15 == i as u16 && !self.link(site, site, (e >> 11) as i16) {
                return false;
            }
        }
        true
    }
}
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct Sig([u16; 9]);

fn frames(n: usize, top: bool) -> Map<Sig, i32> {
    let mut best = Map::default();
    fn rec(ms: &mut Vec<u8>, n: usize, top: bool, best: &mut Map<Sig, i32>) {
        let ok = |a: u8, b: u8| b & ((a << 1) | (a >> 1)) == 0;
        if ms.len() < n {
            for m in 0..8 {
                if ms.last().is_none_or(|&a| ok(a, m)) {
                    ms.push(m);
                    rec(ms, n, top, best);
                    ms.pop();
                }
            }
            return;
        }
        if !ok(ms[n - 1], ms[0]) {
            return;
        }
        let mut u = Uf::new();
        for (c, &m) in ms.iter().enumerate() {
            let r = if top { c / 3 } else { (c + 1) / 3 };
            if (m & 1 != 0 || c % 3 == usize::from(top))
                && !u.link(3 * c, 3 * n + r % (n / 3), (r / (n / 3)) as i16)
            {
                return;
            }
            for i in 0..3 {
                if i > 0 && m & (3 << (i - 1)) != 0 && !u.link(3 * c + i - 1, 3 * c + i, 0) {
                    return;
                }
                if (ms[(c + 1) % n] | m) & (1 << i) != 0
                    && !u.link(3 * c + i, 3 * ((c + 1) % n) + i, ((c + 1) / n) as i16)
                {
                    return;
                }
            }
        }
        let sig = u.sig(&(3 * n..3 * n + n / 3).collect::<Vec<_>>());
        let score: i32 = ms.iter().map(|m| m.count_ones() as i32).sum();
        best.entry(sig)
            .and_modify(|x| *x = score.max(*x))
            .or_insert(score);
    }
    rec(&mut vec![], n, top, &mut best);
    best
}

struct Interner {
    ids: Map<Sig, u32>,
    sigs: Vec<Sig>,
}
impl Interner {
    fn new() -> Self {
        Self {
            ids: Map::default(),
            sigs: vec![],
        }
    }
    fn id(&mut self, s: Sig) -> u32 {
        if let Some(&i) = self.ids.get(&s) {
            return i;
        }
        let i = self.sigs.len() as u32;
        self.sigs.push(s);
        self.ids.insert(s, i);
        i
    }
}
fn key(a: u16, b: u16, s: u32) -> u64 {
    (a as u64) << 32 | (b as u64) << 48 | s as u64
}
fn run(n: usize, lo: i32, hi: i32) {
    let p = n / 3;
    assert!(n == 6 || n == 9);
    let oldsites: Vec<_> = (0..n).collect();
    let newsites: Vec<_> = (n..2 * n).collect();
    let asites: Vec<_> = (1..n).step_by(3).collect();
    let bsites: Vec<_> = (0..n).step_by(3).collect();
    let a = asites.iter().fold(0, |v, i| v | (1 << i));
    let b = bsites.iter().fold(0, |v, i| v | (1 << i));
    let mut intern = Interner::new();
    let mut dp = Map::default();
    let top = frames(n, true);
    let bottom = frames(n, false);
    println!("frame signatures {}/{}", top.len(), bottom.len());
    for (s, v) in top {
        let mut u = Uf::new();
        assert!(u.load(s, &asites));
        for &i in &asites {
            assert!(u.link(i, i - 1, 0))
        }
        dp.insert(key(a, a, intern.id(u.sig(&oldsites))), v);
    }
    let all = (1u16 << n) - 1;
    let rot = |m: u16| (m << 1) & all | m >> (n - 1);
    let free: Vec<_> = (0..=all).filter(|&m| m & rot(m) == 0).collect();
    let mut cache = Map::default();
    let mut cert = None;
    for d in lo - 2..=hi + 1 {
        let mut next = Map::default();
        let mut open = 0;
        let mut req = 0;
        for c in 0..n {
            let r = d + (c % 3) as i32;
            if (lo..=hi).contains(&r) {
                open |= 1 << c
            } else if c % 3 == usize::from(r < lo) {
                req |= 1 << c
            }
        }
        let masks: Vec<_> = free.iter().copied().filter(|m| m & !open == req).collect();
        for (&k, &score) in &dp {
            let aa = (k >> 32) as u16;
            let old = (k >> 48) as u16;
            let sid = k as u32;
            for &m in &masks {
                if aa & rot(m) != 0 {
                    continue;
                }
                let t = *cache.entry(key(old, m, sid)).or_insert_with(|| {
                    let mut u = Uf::new();
                    assert!(u.load(intern.sigs[sid as usize], &oldsites));
                    for c in 0..n {
                        if (old | m) & (1 << c) != 0 && !u.link(c, n + c, 0) {
                            return u32::MAX;
                        }
                        let j = (c + n - 1) % n;
                        if (old >> c | m >> j) & 1 != 0 && !u.link(c, n + j, -i16::from(c == 0)) {
                            return u32::MAX;
                        }
                    }
                    intern.id(u.sig(&newsites))
                });
                if t != u32::MAX {
                    let v = score + (m & open).count_ones() as i32;
                    next.entry(key(old, m, t))
                        .and_modify(|s| *s = v.max(*s))
                        .or_insert(v);
                }
            }
        }
        let stable = open == all
            && dp.len() == next.len()
            && dp
                .iter()
                .all(|(k, &v)| next.get(k) == Some(&(v + p as i32)));
        if stable {
            cert = Some(d)
        }
        println!(
            "slice {d} states {} max {} stable {stable}",
            next.len(),
            next.values().max().unwrap()
        );
        std::io::stdout().flush().unwrap();
        assert!(
            next.len() < 5_000_000 && cache.len() < 25_000_000,
            "memory guard; inconclusive"
        );
        dp = next;
    }
    let mut best = i32::MIN;
    for (k, v) in dp {
        if (k >> 48) as u16 != b {
            continue;
        }
        let mut u = Uf::new();
        assert!(u.load(intern.sigs[k as u32 as usize], &oldsites));
        if !bsites.iter().all(|&i| u.link(i, i + 1, 0)) {
            continue;
        }
        for (&bot, &s) in &bottom {
            let mut u = u.clone();
            if u.load(bot, &bsites) {
                best = best.max(v + s)
            }
        }
    }
    let debit = (hi - lo + 1) * p as i32;
    println!("period {p}, selected {best}, debit {debit}, net {}, target {}, vector certificate {cert:?}",best-debit,8*p);
}
fn main() {
    let a: Vec<i32> = std::env::args()
        .skip(1)
        .map(|x| x.parse().unwrap())
        .collect();
    run(3 * a[0] as usize, a[1], a[2])
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn restriction_retains_offset_and_closed_cycle() {
        let mut u = Uf::new();
        assert!(u.link(4, 2, -1) && u.link(2, 0, 0));
        let s = u.sig(&[0, 4]);
        let mut restored = Uf::new();
        assert!(restored.load(s, &[1, 8]));
        assert!(!restored.link(1, 8, 1)); // same physical path closes a finite cycle
        assert!(restored.link(1, 8, 0)); // winding cycle; OK on the cover
        let s = restored.sig(&[8]);
        let mut next = Uf::new();
        assert!(next.load(s, &[3]) && next.link(4, 4, 1));
        assert!(!next.link(3, 4, 0)); // two winding components cannot be merged
    }
}
