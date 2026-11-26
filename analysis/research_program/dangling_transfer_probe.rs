//! Probe (not a proof) for physical straight-window transfer dimensions.
//! Input: four labelled tiles per line in Lean Port.Quad order.
//! Usage: dangling-transfer-probe QUADS.txt WIDTH HEIGHT
//! Each output is the number of consecutive forced plain tiles from the
//! top in that column, after saturating the four seam passes.
use std::{collections::HashMap, env, fs};

fn main() {
    let argv: Vec<_> = env::args().collect();
    let w: usize = argv[2].parse().unwrap();
    let h: usize = argv[3].parse().unwrap();
    assert!((1..=22).contains(&w) && (1..=54).contains(&h));
    let bank = fs::read_to_string(&argv[1]).unwrap();
    let qs: Vec<[u32; 4]> = bank
        .lines()
        .map(|l| {
            l.split_whitespace()
                .map(|s| s.parse().unwrap())
                .collect::<Vec<_>>()
                .try_into()
                .unwrap()
        })
        .collect();
    let mut keys = HashMap::new();
    let edges: Vec<[usize; 4]> = qs
        .iter()
        .map(|&[a, b, c, d]| {
            [(a, b), (c, d), (a, c), (b, d)].map(|e| {
                let n = keys.len();
                *keys.entry(e).or_insert(n)
            })
        })
        .collect();
    let all: Vec<_> = (0..qs.len()).collect();
    let top: Vec<_> = all
        .iter()
        .copied()
        .filter(|&i| {
            [qs[i][0], qs[i][2]]
                .iter()
                .all(|v| v >> 12 == 73 && (v >> 9) & 7 == 0)
        })
        .collect();
    let mut grid: Vec<_> = (0..h * w)
        .map(|i| if i < w { top.clone() } else { all.clone() })
        .collect();
    let mut epoch = 0usize;
    let mut seen = vec![0usize; keys.len()];
    loop {
        let mut changed = false;
        let mut apply = |src: usize, dst: usize, s: usize, t: usize| {
            epoch += 1;
            for &i in &grid[src] {
                seen[edges[i][s]] = epoch;
            }
            let n = grid[dst].len();
            grid[dst].retain(|&i| seen[edges[i][t]] == epoch);
            changed |= n != grid[dst].len();
        };
        for j in 0..h {
            for i in 0..w - 1 {
                apply(j * w + i, j * w + i + 1, 1, 0);
            }
        }
        for j in 0..h - 1 {
            for i in 0..w {
                apply(j * w + i, (j + 1) * w + i, 3, 2);
            }
        }
        for j in (0..h).rev() {
            for i in (1..w).rev() {
                apply(j * w + i, j * w + i - 1, 0, 1);
            }
        }
        for j in (1..h).rev() {
            for i in (0..w).rev() {
                apply(j * w + i, (j - 1) * w + i, 2, 3);
            }
        }
        if !changed {
            break;
        }
    }
    let depth: Vec<_> = (0..w)
        .map(|i| {
            (0..h)
                .take_while(|j| grid[j * w + i].iter().all(|&n| qs[n][0] >> 12 == 73))
                .count()
        })
        .collect();
    println!("{depth:?}");
}
