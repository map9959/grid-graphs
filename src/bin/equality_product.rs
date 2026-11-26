//! Propagate the physical connectivity across tight eight-row product arcs.
use fxhash::{FxHashMap as Map, FxHashSet as Set};
use serde::Deserialize;
use std::io::{self, Read};

#[derive(Deserialize)]
struct Input {
    tiles: Vec<(u32, u32, Vec<u8>)>,
    arcs: Vec<(usize, usize, usize)>,
}
#[derive(Clone, Copy, Hash, Eq, PartialEq)]
struct Cut {
    mask: u32,
    part: [u8; 18],
}
fn advance(s: Cut, t: &(u32, u32, Vec<u8>)) -> Option<Cut> {
    // Previous components 0..17; current tile components 18..53.
    let mut p: [u8; 54] = std::array::from_fn(|i| i as u8);
    fn root(p: &[u8], mut i: u8) -> u8 {
        while i != p[i as usize] {
            i = p[i as usize]
        }
        i
    }
    let mut edges = s.mask | t.0 | (1 << 17); // common root identified once
    while edges != 0 {
        let i = edges.trailing_zeros() as usize;
        let a = root(&p, s.part[i]);
        let b = root(&p, 18 + t.2[i]);
        if a == b {
            return None;
        }
        p[b as usize] = a;
        edges &= edges - 1;
    }
    let mut name = [255; 54];
    let mut k = 0;
    let part = std::array::from_fn(|i| {
        let a = root(&p, 18 + t.2[18 + i]) as usize;
        if name[a] == 255 {
            name[a] = k;
            k += 1
        }
        name[a]
    });
    Some(Cut { mask: t.1, part })
}
fn main() {
    let mut txt = String::new();
    io::stdin().read_to_string(&mut txt).unwrap();
    let g: Input = serde_json::from_str(&txt).unwrap();
    let mut adj: Map<usize, Vec<(usize, usize)>> = Map::default();
    for (x, y, t) in g.arcs {
        adj.entry(x).or_default().push((y, t));
    }
    let fresh = Cut {
        mask: 0,
        part: std::array::from_fn(|i| i as u8),
    };
    let mut layer: Set<_> = adj.keys().map(|&x| (x, fresh)).collect();
    let mut cache = Map::default();
    let mut predecessors: Vec<Map<(usize, Cut), ((usize, Cut), usize)>> = vec![];
    for n in 1..=60 {
        let mut next = Set::default();
        let mut pred = Map::default();
        for &(x, s) in &layer {
            for &(y, t) in &adj[&x] {
                if let Some(ns) = *cache
                    .entry((s, t))
                    .or_insert_with(|| advance(s, &g.tiles[t]))
                {
                    if next.insert((y, ns)) {
                        pred.insert((y, ns), ((x, s), t));
                    }
                }
            }
        }
        println!(
            "{} physical equality blocks: {} reachable states",
            n,
            next.len()
        );
        if next.is_empty() {
            let mut end = *layer.iter().next().unwrap();
            let mut path = Vec::new();
            for old in predecessors.iter().rev() {
                let (before, t) = old[&end];
                path.push(t);
                end = before;
            }
            path.reverse();
            println!("longest physical walk: {:?}", path);
            println!("EXCLUDED: no arbitrarily repeatable equality walk");
            return;
        }
        if layer == next {
            println!("stabilized, needs cycle reconstruction");
            return;
        }
        assert!(
            next.len() < 2_000_000 && cache.len() < 4_000_000,
            "resource guard: inconclusive"
        );
        layer = next;
        predecessors.push(pred);
    }
    println!("length guard: inconclusive");
}
