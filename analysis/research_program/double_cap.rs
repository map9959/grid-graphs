//! Two independently variable caps, with the rail components kept separate.
//! Run: rustc -O double_cap.rs -o target/double_cap; target/double_cap 2 3 110
use std::collections::HashMap;
type Key = (u16, u64);
fn root(p: &[u8; 32], mut a: u8) -> u8 {
    while p[a as usize] != a {
        a = p[a as usize]
    }
    a
}
fn edge(p: &mut [u8; 32], a: u8, b: u8) -> bool {
    let x = root(p, a);
    let y = root(p, b);
    p[x as usize] = y;
    x != y
}
fn trans(h: usize, k: usize, (old, pkey): Key, phase: usize, first: bool, bars: usize) -> Vec<Key> {
    let d = h + k;
    let nn = 3 + d;
    let mut init = std::array::from_fn(|i| i as u8);
    for i in 0..nn {
        init[i] = ((pkey >> (4 * i)) & 15) as u8
    }
    // Terminals 0,1 are the two full bars. Terminal 2 is the rail
    // component shared by all teeth at distance <=1 from its column.
    let rail = if phase == 2 { (nn + d) as u8 } else { 2 };
    let mut out = Vec::new();
    for m in 0u16..(1 << d) {
        let mut invalid=false;
        for (start,len) in [(0,h),(h,k)] {
            let mask=(1u16<<len)-1;let before=(old>>start)&mask;let after=(m>>start)&mask;
            if !first && after&((before<<1)|(before>>1))!=0 {invalid=true;break}
        }
        if invalid {continue}
        let mut p = init;
        let mut ok = true;
        for (start, len, bar) in [(0, h, 0u8), (h, k, 1u8)] {
            if len==0 && phase==0 && bars&(1<<bar)!=0 {ok &= edge(&mut p,rail,bar)}
            for z in 0..len {
                let i = start + z;
                let dest = (nn + i) as u8;
                let marked = (m >> i) & 1 != 0;
                if !first && (marked || (old >> i) & 1 != 0) {
                    ok &= edge(&mut p, (3 + i) as u8, dest)
                }
                if z == 0 && (marked || phase == 0) {
                    ok &= edge(&mut p, rail, dest)
                }
                if z + 1 == len && marked && bars&(1<<bar)!=0 {
                    ok &= edge(&mut p, bar, dest)
                }
                if z + 1 < len && (m >> i) & 3 != 0 {
                    ok &= edge(&mut p, dest, dest + 1)
                }
                if !ok {
                    break;
                }
            }
            if !ok {
                break;
            }
        }
        if !ok {
            continue;
        }
        let mut reps = [255u8; 32];
        let mut key = 0u64;
        for i in 0..nn {
            let a = match i {
                0 => 0,
                1 => 1,
                2 => rail,
                _ => (nn + i - 3) as u8,
            };
            let r = root(&p, a) as usize;
            if reps[r] == 255 {
                reps[r] = i as u8
            }
            key |= (reps[r] as u64) << (4 * i);
        }
        out.push((m, key));
    }
    out
}
fn main() {
    let args: Vec<usize> = std::env::args()
        .skip(1)
        .map(|s| s.parse().unwrap())
        .collect();
    let (h, k, n) = (args[0], args[1], args[2]);
    let bars=args.get(3).copied().unwrap_or(3);
    assert!(bars<4 && h+k>0 && h+k<=11);
    let init = (0, (0..3 + h + k).map(|i| (i as u64) << (4 * i)).sum());
    let mut dp = HashMap::from([(init, 0i32)]);
    let mut cache = HashMap::new();
    let mut profiles = Vec::new();
    for j in 0..n {
        let mut nd = HashMap::new();
        for (&s, &v) in &dp {
            let opts = cache
                .entry((s, j % 3, j == 0))
                .or_insert_with(|| trans(h, k, s, j % 3, j == 0,bars));
            for &u in opts.iter() {
                let z = v + u.0.count_ones() as i32;
                let e = nd.entry(u).or_insert(z);
                *e = (*e).max(z)
            }
        }
        dp = nd;
        if j % 3 == 0 && j >= 3 + h + k {
            let width = j as i32 + 1;
            let t = j as i32 / 3;
            let mx = *dp.values().max().unwrap();
            let nb=bars.count_ones() as i32;
            let total = nb * width + (width - 2*nb - (h + k) as i32) * (t + 1) + mx;
            let old = 3 * t * t + 5 * t + (3 * t - 13).div_euclid(10);
            println!(
                "n={width} states={} cap={mx} total={total} gain={}",
                dp.len(),
                total - old
            );
            let norm: HashMap<_, _> = dp.iter().map(|(s, v)| (*s, v - mx)).collect();
            if let Some((w, m, _)) = profiles.iter().find(|(_, _, a)| *a == norm) {
                println!(
                    "full vector repeats at widths {w} and {width}, shift {}",
                    mx - m
                );
                break;
            }
            profiles.push((width, mx, norm))
        }
    }
}
