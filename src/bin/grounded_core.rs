//! Transfer the three free columns including all induced connections. Roots
//! unable to spend an outgoing edge are tied to one common external ground.
use fxhash::FxHashMap as Map;
use std::io::Write;
const H: usize = match option_env!("GROUND_HEIGHT") {
    Some(s) => {
        let b = s.as_bytes();
        if b.len() == 2 {
            10 * (b[0] - b'0') as usize + (b[1] - b'0') as usize
        } else {
            (b[0] - b'0') as usize
        }
    }
    None => 9,
};
const LO: i32 = -((H - 3) as i32 / 2);
const HI: i32 = LO + H as i32 - 1;
const N: usize = H + 6;
type Part = [u8; N + 3]; // ground, A, B, then sites at local rows LO-3..HI+3
#[derive(Clone)]
struct Uf([u8; 2 * (N + 3)]);
impl Uf {
    fn new() -> Self {
        Self(std::array::from_fn(|i| i as u8))
    }
    fn root(&self, mut i: usize) -> usize {
        while self.0[i] as usize != i {
            i = self.0[i] as usize
        }
        i
    }
    fn link(&mut self, a: usize, b: usize) -> bool {
        let (x, y) = (self.root(a), self.root(b));
        if x == y {
            return false;
        }
        self.0[y] = x as u8;
        true
    }
    fn sig(&self, sites: &[usize; N + 3]) -> Part {
        let mut reps = [255; 2 * (N + 3)];
        std::array::from_fn(|i| {
            let a = self.root(sites[i]);
            if reps[a] == 255 {
                reps[a] = i as u8
            }
            reps[a]
        })
    }
}
fn fixed(c: usize, r: i32) -> bool {
    (c == 0 && r > HI) || (c == 1 && r < LO)
}
fn label(c: usize, r: i32) -> usize {
    if (c as i32 - 1).abs() + 0.max(r - LO + 1) <= 1 {
        return 1;
    }
    if c as i32 + 0.max(HI + 1 - r) <= 1 {
        return 2;
    }
    // At c=2, rows >= HI+4 would belong to B_next; never needed.
    (3 + r - LO + 3) as usize
}
fn f(m: u16, c: usize, r: i32) -> bool {
    if (LO..=HI).contains(&r) {
        m & (1 << (r - LO)) != 0
    } else {
        fixed(c, r)
    }
}
fn main() {
    let steps: usize = std::env::args()
        .nth(1)
        .unwrap_or("10".into())
        .parse()
        .unwrap();
    let mut dp = Map::default();
    let start: Part = std::array::from_fn(|i| i as u8);
    dp.insert((0u16, start), 0i32);
    let mut snaps: Vec<Map<(u16, Part), i32>> = vec![];
    // Internal vertical edges in the incoming column are completely
    // determined by its mask. Compose their partition with previous slice.
    let base = N + 3;
    println!("nine-row control generalized: height {H}, local rows {LO}..{HI}");
    for t in 0..3 * steps {
        let c = t % 3;
        let old = (c + 2) % 3;
        let delta = if c == 0 { 3 } else { 0 };
        let mut next = Map::default();
        let mut grouped = vec![Vec::new(); 1 << H];
        for (&(m, ref p), &v) in &dp {
            grouped[m as usize].push((p, v));
        }
        for m in 0u16..1 << H {
            let mut prefab = Uf::new();
            let newsite = |r| base + label(c, r);
            let mut good = true;
            for r in LO - 1..=HI {
                if (f(m, c, r) || f(m, c, r + 1))
                    && !fixed(c, r)
                    && !fixed(c, r + 1)
                    && !prefab.link(newsite(r), newsite(r + 1))
                {
                    good = false;
                    break;
                }
            }
            if !good {
                continue;
            }
            for flags in 0u8..(if c == 0 { 4 } else { 1 }) {
                let mut pre = prefab.clone();
                if c == 0 {
                    for b in 0..2 {
                        if flags & (1 << b) != 0 && !pre.link(base, base + 1 + b) {
                            good = false
                        }
                    }
                    if !good {
                        good = true;
                        continue;
                    }
                }
                let right = (m as u32) << delta;
                let allowed = (((1u32 << H) - 1) & !((right << 1) | (right >> 1))) as u16;
                let mut prev = Some(allowed);
                while let Some(pm) = prev {
                    prev = if pm == 0 {
                        None
                    } else {
                        Some((pm - 1) & allowed)
                    };
                    for &(p, v) in &grouped[pm as usize] {
                        let mut u = pre.clone();
                        u.0[..base].copy_from_slice(p);
                        u.link(0, base);
                        if c != 0 && (!u.link(1, base + 1) || !u.link(2, base + 2)) {
                            continue;
                        }
                        let mut ok = true;
                        for r in LO - delta..=HI {
                            let s = r + delta;
                            if (f(pm, old, s) || f(m, c, r))
                                && !fixed(old, s)
                                && !fixed(c, r)
                                && !u.link(
                                    if t == 0 {
                                        (3 + s - LO + 3) as usize
                                    } else {
                                        label(old, s)
                                    },
                                    newsite(r),
                                )
                            {
                                ok = false;
                                break;
                            }
                        }
                        if !ok {
                            continue;
                        }
                        let sites = std::array::from_fn(|i| {
                            if i < 3 {
                                base + i
                            } else {
                                newsite(LO - 3 + (i - 3) as i32)
                            }
                        });
                        let sig = u.sig(&sites);
                        let weight = v
                            + m.count_ones() as i32
                            + if c == 0 {
                                flags.count_ones() as i32 - 2 - H as i32
                            } else {
                                0
                            };
                        next.entry((m, sig))
                            .and_modify(|x: &mut i32| *x = (*x).max(weight))
                            .or_insert(weight);
                    }
                }
            }
        }
        dp = next;
        println!(
            "column {} phase {} states {} max {}",
            t + 1,
            c,
            dp.len(),
            dp.values().max().unwrap()
        );
        std::io::stdout().flush().unwrap();
        assert!(dp.len() < 2_000_000, "state guard: inconclusive");
        if c == 2 {
            for (j, old) in snaps.iter().enumerate() {
                if old.len() == dp.len() {
                    let diff = dp.values().max().unwrap() - old.values().max().unwrap();
                    if old.iter().all(|(k, v)| dp.get(k) == Some(&(v + diff))) {
                        println!(
                            "full vector recurrence: {diff} score per {} blocks",
                            snaps.len() - j
                        );
                        return;
                    }
                }
            }
            snaps.push(dp.clone());
        }
    }
}
