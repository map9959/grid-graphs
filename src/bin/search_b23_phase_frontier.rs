//! Exact bidirectional row-frontier search over exported B23 phase domains.

use std::env;
use std::fs;
use std::hash::BuildHasherDefault;
use std::process;
use std::time::Instant;

use fxhash::FxHasher;
use hashbrown::{HashMap, HashSet};

const N: usize = 23;
const FACE_COLUMNS: usize = N - 1;
const LABEL_BITS: usize = 5;
const CUT: usize = 11;
const LIMIT: u16 = 335;

type FastSet<T> = HashSet<T, BuildHasherDefault<FxHasher>>;
type FastMap<K, V> = HashMap<K, V, BuildHasherDefault<FxHasher>>;

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct State {
    labels: u128,
    previous_u: u32,
    cost: u16,
    cycles: u16,
}

#[derive(Clone)]
struct Dsu {
    parent: [u8; 2 * N],
}

impl Dsu {
    fn new() -> Self {
        let mut parent = [0; 2 * N];
        for (index, item) in parent.iter_mut().enumerate() {
            *item = index as u8;
        }
        Self { parent }
    }

    fn root(&mut self, mut node: usize) -> usize {
        while self.parent[node] as usize != node {
            self.parent[node] = self.parent[self.parent[node] as usize];
            node = self.parent[node] as usize;
        }
        node
    }

    fn union(&mut self, a: usize, b: usize) -> bool {
        let a = self.root(a);
        let b = self.root(b);
        if a == b {
            return false;
        }
        self.parent[b] = a as u8;
        true
    }
}

fn label_at(labels: u128, slot: usize) -> usize {
    ((labels >> (LABEL_BITS * slot)) & 31) as usize
}

fn partition_components(labels: u128) -> usize {
    (0..N).map(|slot| label_at(labels, slot)).max().unwrap() + 1
}

fn initialize_partition(dsu: &mut Dsu, labels: u128) {
    let mut representatives = [usize::MAX; N];
    for slot in 0..N {
        let label = label_at(labels, slot);
        if representatives[label] == usize::MAX {
            representatives[label] = slot;
        } else {
            dsu.union(slot, representatives[label]);
        }
    }
}

fn canonical_partition(dsu: &mut Dsu, nodes: impl Iterator<Item = usize>) -> u128 {
    let mut roots = [usize::MAX; N];
    let mut next_label = 0usize;
    let mut packed = 0u128;
    for (slot, node) in nodes.enumerate() {
        let root = dsu.root(node);
        let label = if let Some(label) = roots[..next_label].iter().position(|&item| item == root) {
            label
        } else {
            roots[next_label] = root;
            next_label += 1;
            next_label - 1
        };
        packed |= (label as u128) << (LABEL_BITS * slot);
    }
    packed
}

fn advance_row(state: State, current_u: u32, logical_row: usize) -> Option<State> {
    let has_old = logical_row > 0;
    let has_new = logical_row + 1 < N;
    let old_start = 1usize;
    let new_start = old_start + if has_old { FACE_COLUMNS } else { 0 };
    let mut dsu = Dsu::new();
    if has_old {
        initialize_partition(&mut dsu, state.labels);
    }
    let mut cycles = state.cycles;
    let mut add_edge = |dsu: &mut Dsu, a: usize, b: usize| {
        if !dsu.union(a, b) {
            cycles += 1;
        }
    };

    if has_old {
        let both_u = state.previous_u & current_u;
        for column in 0..N {
            if both_u & (1 << column) == 0 {
                continue;
            }
            let left = if column == 0 {
                0
            } else {
                old_start + column - 1
            };
            let right = if column + 1 == N {
                0
            } else {
                old_start + column
            };
            add_edge(&mut dsu, left, right);
        }
    }
    let adjacent_u = current_u & (current_u >> 1);
    for column in 0..FACE_COLUMNS {
        if adjacent_u & (1 << column) == 0 {
            continue;
        }
        let above = if has_old { old_start + column } else { 0 };
        let below = if has_new { new_start + column } else { 0 };
        add_edge(&mut dsu, above, below);
    }

    if has_old {
        let mut retained = [false; 2 * N];
        let out_root = dsu.root(0);
        retained[out_root] = true;
        if has_new {
            for node in new_start..new_start + FACE_COLUMNS {
                let root = dsu.root(node);
                retained[root] = true;
            }
        }
        for node in old_start..old_start + FACE_COLUMNS {
            let root = dsu.root(node);
            if !retained[root] {
                return None;
            }
        }
    }

    let labels = if has_new {
        canonical_partition(
            &mut dsu,
            std::iter::once(0).chain(new_start..new_start + FACE_COLUMNS),
        )
    } else {
        0
    };
    Some(State {
        labels,
        previous_u: current_u,
        cost: state.cost + current_u.count_ones() as u16,
        cycles,
    })
}

fn rank_deficit_impossible(state: State, rows: usize) -> bool {
    let introduced = 1 + rows.min(N - 1) * FACE_COLUMNS;
    let current_rank = introduced - partition_components(state.labels);
    current_rank + 2 * ((LIMIT - state.cost) as usize) < FACE_COLUMNS * FACE_COLUMNS
}

fn minimum_costs(domains: &[Vec<u32>]) -> (Vec<u16>, Vec<u16>) {
    let minimum: Vec<u16> = domains
        .iter()
        .map(|domain| {
            domain
                .iter()
                .map(|mask| mask.count_ones() as u16)
                .min()
                .unwrap()
        })
        .collect();
    let mut prefix = vec![0; N + 1];
    for row in 0..N {
        prefix[row + 1] = prefix[row] + minimum[row];
    }
    let mut suffix = vec![0; N + 1];
    for row in (0..N).rev() {
        suffix[row] = suffix[row + 1] + minimum[row];
    }
    (prefix, suffix)
}

fn expand_side(
    side: &str,
    rows: impl Iterator<Item = usize>,
    domains: &[Vec<u32>],
    prefix: &[u16],
    suffix: &[u16],
) -> Vec<State> {
    let mut layer = vec![State {
        labels: 0,
        previous_u: 0,
        cost: 0,
        cycles: 0,
    }];
    for (depth, row) in rows.enumerate() {
        let started = Instant::now();
        let other_minimum = if side == "top" {
            suffix[row + 1]
        } else {
            prefix[row]
        };
        let mut next = FastSet::with_capacity_and_hasher(
            layer.len().saturating_mul(4),
            BuildHasherDefault::default(),
        );
        let mut attempted = 0u64;
        let mut live = 0u64;
        for state in layer {
            if state.cost + other_minimum > LIMIT {
                continue;
            }
            for &mask in &domains[row] {
                attempted += 1;
                if state.cost + mask.count_ones() as u16 + other_minimum > LIMIT {
                    continue;
                }
                let Some(outgoing) = advance_row(state, mask, depth) else {
                    continue;
                };
                live += 1;
                if rank_deficit_impossible(outgoing, depth + 1) {
                    continue;
                }
                next.insert(outgoing);
            }
        }
        eprintln!(
            "side={side} row={row} domain={} attempted={attempted} live={live} states={} elapsed={:.3}s",
            domains[row].len(), next.len(), started.elapsed().as_secs_f64()
        );
        layer = next.into_iter().collect();
    }
    layer
}

fn merge_components(top: State, bottom: State) -> usize {
    let mut dsu = Dsu::new();
    let mut representatives = [[usize::MAX; N]; 2];
    for (side, labels) in [top.labels, bottom.labels].into_iter().enumerate() {
        for node in 0..N {
            let label = label_at(labels, node);
            if representatives[side][label] == usize::MAX {
                representatives[side][label] = node;
            } else {
                dsu.union(node, representatives[side][label]);
            }
        }
    }
    let crossing = top.previous_u & bottom.previous_u;
    for column in 0..N {
        if crossing & (1 << column) == 0 {
            continue;
        }
        let left = if column == 0 { 0 } else { column };
        let right = if column + 1 == N { 0 } else { column + 1 };
        dsu.union(left, right);
    }
    let mut roots = [usize::MAX; N];
    let mut count = 0;
    for node in 0..N {
        let root = dsu.root(node);
        if !roots[..count].contains(&root) {
            roots[count] = root;
            count += 1;
        }
    }
    count
}

fn join_states(top: &[State], bottom: &[State], budget: u16) -> (u64, u64, usize) {
    let mut by_cost: FastMap<u16, Vec<State>> = FastMap::with_hasher(BuildHasherDefault::default());
    for &state in bottom {
        by_cost.entry(state.cost).or_default().push(state);
    }
    let mut tested = 0u64;
    let mut connected = 0u64;
    let mut best = N;
    for &top_state in top {
        let Some(bottom_states) = by_cost.get(&budget.saturating_sub(top_state.cost)) else {
            continue;
        };
        if top_state.cost > budget {
            continue;
        }
        for &bottom_state in bottom_states {
            tested += 1;
            let components = merge_components(top_state, bottom_state);
            best = best.min(components);
            if components == 1 {
                connected += 1;
            }
        }
    }
    (tested, connected, best)
}

fn read_domains(path: &str) -> Result<Vec<Vec<u32>>, String> {
    let text = fs::read_to_string(path).map_err(|error| error.to_string())?;
    let domains: Result<Vec<Vec<u32>>, _> = text
        .lines()
        .map(|line| line.split(',').map(str::parse).collect())
        .collect();
    let domains = domains.map_err(|error| format!("invalid domain mask: {error}"))?;
    if domains.len() != N || domains.iter().any(Vec::is_empty) {
        return Err(format!("expected {N} nonempty row domains"));
    }
    Ok(domains)
}

fn run(path: &str) -> Result<(), String> {
    let domains = read_domains(path)?;
    let (prefix, suffix) = minimum_costs(&domains);
    let started = Instant::now();
    let top = expand_side("top", 0..CUT, &domains, &prefix, &suffix);
    let bottom = expand_side("bottom", (CUT..N).rev(), &domains, &prefix, &suffix);
    for budget in [335, 333] {
        let join_started = Instant::now();
        let (tested, connected, best) = join_states(&top, &bottom, budget);
        println!(
            "budget={budget} result={} tested={tested} connected={connected} best_components={best} join_elapsed={:.3}s",
            if connected > 0 { "SAT" } else { "UNSAT_IN_LANGUAGE" },
            join_started.elapsed().as_secs_f64()
        );
    }
    println!(
        "top_states={} bottom_states={} elapsed={:.3}s",
        top.len(),
        bottom.len(),
        started.elapsed().as_secs_f64()
    );
    Ok(())
}

fn main() {
    let path = env::args().nth(1).unwrap_or_else(|| {
        eprintln!("usage: search_b23_phase_frontier DOMAIN_FILE");
        process::exit(2);
    });
    if let Err(error) = run(&path) {
        eprintln!("error: {error}");
        process::exit(2);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn one_row_matches_simple_out_connections() {
        let state = State {
            labels: 0,
            previous_u: 0,
            cost: 0,
            cycles: 0,
        };
        let outgoing = advance_row(state, (1 << N) - 1, 0).unwrap();
        assert_eq!(outgoing.cost, N as u16);
        assert_eq!(partition_components(outgoing.labels), 1);
    }

    #[test]
    fn disconnected_old_component_is_rejected() {
        let labels = (1..N).fold(0u128, |packed, slot| {
            packed | (1u128 << (LABEL_BITS * slot))
        });
        let state = State {
            labels,
            previous_u: 0,
            cost: 0,
            cycles: 0,
        };
        assert!(advance_row(state, 0, 1).is_none());
    }
}
