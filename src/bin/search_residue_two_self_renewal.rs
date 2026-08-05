//! Exact cap-to-cap B20-to-B23 self-renewal search from a Python manifest.

use std::collections::{BTreeMap, HashSet};
use std::env;
use std::fs;
use std::hash::BuildHasherDefault;
use std::process;
use std::time::Instant;

use fxhash::FxHasher;
use hashbrown::HashMap;
use serde::Deserialize;

type FastMap<K, V> = HashMap<K, V, BuildHasherDefault<FxHasher>>;

#[derive(Clone, Debug, Deserialize)]
struct Manifest {
    schema: String,
    target_n: usize,
    cut: usize,
    u_limit: u32,
    join_budgets: Vec<u32>,
    top_start_row: usize,
    bottom_start_row: usize,
    mask_domains: Vec<MaskDomain>,
    signature_states: Vec<SignatureSpec>,
    signature_transitions: Vec<TransitionSpec>,
    top_seeds: Vec<SeedSpec>,
    bottom_seeds: Vec<SeedSpec>,
}

#[derive(Clone, Debug, Deserialize)]
struct MaskDomain {
    id: u32,
    masks: Vec<u64>,
}

#[derive(Clone, Debug, Deserialize)]
struct SignatureSpec {
    id: u32,
    layer: usize,
    lane: u32,
}

#[derive(Clone, Debug, Deserialize)]
struct TransitionSpec {
    row: usize,
    before: u32,
    after: u32,
    domain_id: u32,
    lane: u32,
}

#[derive(Clone, Debug, Deserialize)]
struct SeedSpec {
    signature: u32,
    state: SeedState,
}

#[derive(Clone, Debug, Deserialize)]
struct SeedState {
    previous_u: u64,
    partition: Vec<u8>,
    cost: u32,
    cycles: u32,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct State {
    labels: u128,
    previous_u: u64,
    cost: u32,
    cycles: u32,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct ProductState {
    state: State,
    signature: u32,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct StructuralKey {
    labels: u128,
    previous_u: u64,
    signature: u32,
}

impl ProductState {
    fn key(self) -> StructuralKey {
        StructuralKey {
            labels: self.state.labels,
            previous_u: self.state.previous_u,
            signature: self.signature,
        }
    }
}

struct Dsu {
    parent: Vec<usize>,
}

impl Dsu {
    fn new(size: usize) -> Self {
        Self {
            parent: (0..size).collect(),
        }
    }

    fn root(&mut self, mut node: usize) -> usize {
        while self.parent[node] != node {
            self.parent[node] = self.parent[self.parent[node]];
            node = self.parent[node];
        }
        node
    }

    fn union(&mut self, left: usize, right: usize) -> bool {
        let left = self.root(left);
        let right = self.root(right);
        if left == right {
            return false;
        }
        self.parent[right] = left;
        true
    }
}

fn label_at(labels: u128, slot: usize) -> usize {
    ((labels >> (5 * slot)) & 31) as usize
}

fn pack_partition(partition: &[u8], n: usize) -> Result<u128, String> {
    if partition.len() != n || n > 25 {
        return Err("partition width is invalid or exceeds u128 packing".into());
    }
    let mut next = 0u8;
    let mut seen = [false; 32];
    let mut packed = 0u128;
    for (slot, &label) in partition.iter().enumerate() {
        if label >= 32 {
            return Err("partition label exceeds five-bit packing".into());
        }
        if !seen[label as usize] {
            if label != next {
                return Err("partition labels are not canonical".into());
            }
            seen[label as usize] = true;
            next += 1;
        }
        packed |= (label as u128) << (5 * slot);
    }
    Ok(packed)
}

fn component_count(labels: u128, n: usize) -> usize {
    (0..n).map(|slot| label_at(labels, slot)).max().unwrap() + 1
}

fn initialize_partition(dsu: &mut Dsu, labels: u128, n: usize) {
    let mut representatives = vec![usize::MAX; n];
    for slot in 0..n {
        let label = label_at(labels, slot);
        if representatives[label] == usize::MAX {
            representatives[label] = slot;
        } else {
            dsu.union(slot, representatives[label]);
        }
    }
}

fn canonical_partition(dsu: &mut Dsu, nodes: impl Iterator<Item = usize>) -> u128 {
    let mut roots = Vec::new();
    let mut packed = 0u128;
    for (slot, node) in nodes.enumerate() {
        let root = dsu.root(node);
        let label = roots
            .iter()
            .position(|&item| item == root)
            .unwrap_or_else(|| {
                roots.push(root);
                roots.len() - 1
            });
        packed |= (label as u128) << (5 * slot);
    }
    packed
}

fn advance_row(state: State, current_u: u64, logical_row: usize, n: usize) -> Option<State> {
    let has_old = logical_row > 0;
    let has_new = logical_row + 1 < n;
    let old_start = 1usize;
    let new_start = old_start + if has_old { n - 1 } else { 0 };
    let mut dsu = Dsu::new(1 + usize::from(has_old) * (n - 1) + usize::from(has_new) * (n - 1));
    if has_old {
        initialize_partition(&mut dsu, state.labels, n);
    }
    let mut cycles = state.cycles;
    let mut add_edge = |dsu: &mut Dsu, left: usize, right: usize| {
        if !dsu.union(left, right) {
            cycles += 1;
        }
    };
    if has_old {
        let both_u = state.previous_u & current_u;
        for column in 0..n {
            if both_u & (1 << column) == 0 {
                continue;
            }
            let left = if column == 0 {
                0
            } else {
                old_start + column - 1
            };
            let right = if column + 1 == n {
                0
            } else {
                old_start + column
            };
            add_edge(&mut dsu, left, right);
        }
    }
    let adjacent_u = current_u & (current_u >> 1);
    for column in 0..n - 1 {
        if adjacent_u & (1 << column) == 0 {
            continue;
        }
        let above = if has_old { old_start + column } else { 0 };
        let below = if has_new { new_start + column } else { 0 };
        add_edge(&mut dsu, above, below);
    }
    if has_old {
        let mut retained = vec![false; dsu.parent.len()];
        let out = dsu.root(0);
        retained[out] = true;
        if has_new {
            for node in new_start..new_start + n - 1 {
                let root = dsu.root(node);
                retained[root] = true;
            }
        }
        for node in old_start..old_start + n - 1 {
            let root = dsu.root(node);
            if !retained[root] {
                return None;
            }
        }
    }
    let labels = if has_new {
        canonical_partition(
            &mut dsu,
            std::iter::once(0).chain(new_start..new_start + n - 1),
        )
    } else {
        0
    };
    Some(State {
        labels,
        previous_u: current_u,
        cost: state.cost + current_u.count_ones(),
        cycles,
    })
}

fn rank_deficit_impossible(state: State, rows: usize, n: usize, limit: u32) -> bool {
    if state.cost > limit {
        return true;
    }
    let introduced = 1 + rows.min(n - 1) * (n - 1);
    let rank = introduced - component_count(state.labels, n);
    rank + 2 * ((limit - state.cost) as usize) < (n - 1) * (n - 1)
}

struct Runtime<'a> {
    manifest: &'a Manifest,
    domains: FastMap<u32, &'a [u64]>,
    states: FastMap<u32, &'a SignatureSpec>,
    forward: FastMap<u32, Vec<&'a TransitionSpec>>,
    reverse: FastMap<u32, Vec<&'a TransitionSpec>>,
    min_from_top: FastMap<u32, u32>,
    min_to_bottom: FastMap<u32, u32>,
}

impl<'a> Runtime<'a> {
    fn new(manifest: &'a Manifest) -> Result<Self, String> {
        if manifest.schema != "grid-graphs.residue-two-frontier-manifest.v1" {
            return Err("unsupported manifest schema".into());
        }
        let domains: FastMap<_, _> = manifest
            .mask_domains
            .iter()
            .map(|item| (item.id, item.masks.as_slice()))
            .collect();
        let states: FastMap<_, _> = manifest
            .signature_states
            .iter()
            .map(|item| (item.id, item))
            .collect();
        let mut forward: FastMap<u32, Vec<&TransitionSpec>> = FastMap::default();
        let mut reverse: FastMap<u32, Vec<&TransitionSpec>> = FastMap::default();
        for edge in &manifest.signature_transitions {
            let before = states.get(&edge.before).ok_or("missing before signature")?;
            let after = states.get(&edge.after).ok_or("missing after signature")?;
            if before.layer != edge.row
                || after.layer != edge.row + 1
                || before.lane != edge.lane
                || after.lane != edge.lane
                || !domains.contains_key(&edge.domain_id)
            {
                return Err("transition metadata is inconsistent".into());
            }
            forward.entry(edge.before).or_default().push(edge);
            reverse.entry(edge.after).or_default().push(edge);
        }

        let mut min_from_top = FastMap::default();
        for seed in &manifest.top_seeds {
            let entry = min_from_top
                .entry(seed.signature)
                .or_insert(seed.state.cost);
            *entry = (*entry).min(seed.state.cost);
        }
        for row in manifest.top_start_row..manifest.bottom_start_row {
            for edge in manifest
                .signature_transitions
                .iter()
                .filter(|edge| edge.row == row)
            {
                let Some(&cost) = min_from_top.get(&edge.before) else {
                    continue;
                };
                let minimum = domains[&edge.domain_id]
                    .iter()
                    .map(|mask| mask.count_ones())
                    .min()
                    .unwrap();
                let candidate = cost + minimum;
                let entry = min_from_top.entry(edge.after).or_insert(candidate);
                *entry = (*entry).min(candidate);
            }
        }
        let mut min_to_bottom = FastMap::default();
        for seed in &manifest.bottom_seeds {
            let entry = min_to_bottom
                .entry(seed.signature)
                .or_insert(seed.state.cost);
            *entry = (*entry).min(seed.state.cost);
        }
        for row in (manifest.top_start_row..manifest.bottom_start_row).rev() {
            for edge in manifest
                .signature_transitions
                .iter()
                .filter(|edge| edge.row == row)
            {
                let Some(&cost) = min_to_bottom.get(&edge.after) else {
                    continue;
                };
                let minimum = domains[&edge.domain_id]
                    .iter()
                    .map(|mask| mask.count_ones())
                    .min()
                    .unwrap();
                let candidate = cost + minimum;
                let entry = min_to_bottom.entry(edge.before).or_insert(candidate);
                *entry = (*entry).min(candidate);
            }
        }
        Ok(Self {
            manifest,
            domains,
            states,
            forward,
            reverse,
            min_from_top,
            min_to_bottom,
        })
    }

    fn seed(&self, seed: &SeedSpec) -> Result<ProductState, String> {
        if !self.states.contains_key(&seed.signature) {
            return Err("seed references a missing signature".into());
        }
        Ok(ProductState {
            state: State {
                labels: pack_partition(&seed.state.partition, self.manifest.target_n)?,
                previous_u: seed.state.previous_u,
                cost: seed.state.cost,
                cycles: seed.state.cycles,
            },
            signature: seed.signature,
        })
    }
}

fn retain_minimum(states: &mut FastMap<StructuralKey, ProductState>, candidate: ProductState) {
    let key = candidate.key();
    let old = states.get(&key);
    if old.is_none_or(|old| candidate.state.cost < old.state.cost) {
        states.insert(key, candidate);
    }
}

fn apply_beam(
    states: FastMap<StructuralKey, ProductState>,
    beam: Option<usize>,
    n: usize,
) -> FastMap<StructuralKey, ProductState> {
    let Some(beam) = beam else { return states };
    if states.len() <= beam {
        return states;
    }
    let rank = |item: &ProductState| {
        (
            item.state.cost,
            component_count(item.state.labels, n),
            item.state.labels,
            item.state.previous_u,
        )
    };
    let mut groups: FastMap<u32, Vec<ProductState>> = FastMap::default();
    for item in states.into_values() {
        groups.entry(item.signature).or_default().push(item);
    }
    let quota = (beam / groups.len()).max(1);
    let mut retained = Vec::with_capacity(beam);
    let mut remainder = Vec::new();
    for mut group in groups.into_values() {
        group.sort_unstable_by_key(rank);
        let split = quota.min(group.len());
        remainder.extend(group.drain(split..));
        retained.extend(group);
    }
    if retained.len() < beam {
        remainder.sort_unstable_by_key(rank);
        remainder.truncate(beam - retained.len());
        retained.extend(remainder);
    }
    retained
        .into_iter()
        .map(|item| (item.key(), item))
        .collect()
}

fn expand_side(
    runtime: &Runtime<'_>,
    side: &str,
    beam: Option<usize>,
) -> Result<Vec<ProductState>, String> {
    let manifest = runtime.manifest;
    let seeds = if side == "top" {
        &manifest.top_seeds
    } else {
        &manifest.bottom_seeds
    };
    let mut layer = FastMap::default();
    for seed in seeds {
        retain_minimum(&mut layer, runtime.seed(seed)?);
    }
    let rows: Vec<usize> = if side == "top" {
        (manifest.top_start_row..manifest.cut).collect()
    } else {
        (manifest.cut..manifest.bottom_start_row).rev().collect()
    };
    let initial_depth = if side == "top" {
        manifest.top_start_row
    } else {
        manifest.target_n - manifest.bottom_start_row
    };
    for (offset, row) in rows.into_iter().enumerate() {
        let started = Instant::now();
        let mut next = FastMap::with_capacity_and_hasher(
            layer.len().saturating_mul(4),
            BuildHasherDefault::default(),
        );
        let mut attempted = 0u64;
        let mut live = 0u64;
        for product in layer.into_values() {
            let edges = if side == "top" {
                runtime.forward.get(&product.signature)
            } else {
                runtime.reverse.get(&product.signature)
            };
            let Some(edges) = edges else { continue };
            for edge in edges {
                if edge.row != row {
                    continue;
                }
                let next_signature = if side == "top" {
                    edge.after
                } else {
                    edge.before
                };
                let other_minimum = if side == "top" {
                    runtime.min_to_bottom.get(&next_signature)
                } else {
                    runtime.min_from_top.get(&next_signature)
                };
                let Some(&other_minimum) = other_minimum else {
                    continue;
                };
                for &mask in runtime.domains[&edge.domain_id] {
                    attempted += 1;
                    if product.state.cost + mask.count_ones() + other_minimum > manifest.u_limit {
                        continue;
                    }
                    let Some(outgoing) = advance_row(
                        product.state,
                        mask,
                        initial_depth + offset,
                        manifest.target_n,
                    ) else {
                        continue;
                    };
                    live += 1;
                    if rank_deficit_impossible(
                        outgoing,
                        initial_depth + offset + 1,
                        manifest.target_n,
                        manifest.u_limit,
                    ) {
                        continue;
                    }
                    retain_minimum(
                        &mut next,
                        ProductState {
                            state: outgoing,
                            signature: next_signature,
                        },
                    );
                }
            }
        }
        let before_beam = next.len();
        next = apply_beam(next, beam, manifest.target_n);
        eprintln!(
            "side={side} row={row} attempted={attempted} live={live} structural_states={before_beam} retained={} signatures={} elapsed={:.3}s",
            next.len(),
            next.values().map(|item| item.signature).collect::<HashSet<_>>().len(),
            started.elapsed().as_secs_f64()
        );
        layer = next;
    }
    Ok(layer.into_values().collect())
}

fn merge_components(top: State, bottom: State, n: usize) -> usize {
    let mut dsu = Dsu::new(n);
    let mut representatives = vec![vec![usize::MAX; n]; 2];
    for (side, labels) in [top.labels, bottom.labels].into_iter().enumerate() {
        for node in 0..n {
            let label = label_at(labels, node);
            if representatives[side][label] == usize::MAX {
                representatives[side][label] = node;
            } else {
                dsu.union(node, representatives[side][label]);
            }
        }
    }
    let crossing = top.previous_u & bottom.previous_u;
    for column in 0..n {
        if crossing & (1 << column) == 0 {
            continue;
        }
        let left = if column == 0 { 0 } else { column };
        let right = if column + 1 == n { 0 } else { column + 1 };
        dsu.union(left, right);
    }
    let mut roots = Vec::new();
    for node in 0..n {
        let root = dsu.root(node);
        if !roots.contains(&root) {
            roots.push(root);
        }
    }
    roots.len()
}

fn join(top: &[ProductState], bottom: &[ProductState], budget: u32, n: usize) -> (u64, u64, usize) {
    let mut buckets: FastMap<u32, Vec<State>> = FastMap::default();
    for item in bottom {
        buckets.entry(item.signature).or_default().push(item.state);
    }
    let mut tested = 0u64;
    let mut connected = 0u64;
    let mut best = n;
    for item in top {
        if item.state.cost > budget {
            continue;
        }
        let Some(states) = buckets.get(&item.signature) else {
            continue;
        };
        for &bottom_state in states {
            if item.state.cost + bottom_state.cost > budget {
                continue;
            }
            tested += 1;
            let components = merge_components(item.state, bottom_state, n);
            best = best.min(components);
            connected += u64::from(components == 1);
        }
    }
    (tested, connected, best)
}

fn run(path: &str, beam: Option<usize>) -> Result<(), String> {
    let text = fs::read_to_string(path).map_err(|error| error.to_string())?;
    let manifest: Manifest = serde_json::from_str(&text).map_err(|error| error.to_string())?;
    let runtime = Runtime::new(&manifest)?;
    let started = Instant::now();
    let top = expand_side(&runtime, "top", beam)?;
    let bottom = expand_side(&runtime, "bottom", beam)?;
    let mut top_min: FastMap<u32, u32> = FastMap::default();
    let mut bottom_min: FastMap<u32, u32> = FastMap::default();
    for item in &top {
        let entry = top_min.entry(item.signature).or_insert(item.state.cost);
        *entry = (*entry).min(item.state.cost);
    }
    for item in &bottom {
        let entry = bottom_min.entry(item.signature).or_insert(item.state.cost);
        *entry = (*entry).min(item.state.cost);
    }
    let common_signatures = top_min
        .keys()
        .filter(|signature| bottom_min.contains_key(*signature))
        .count();
    let minimum_join_cost = top_min
        .iter()
        .filter_map(|(signature, top_cost)| {
            bottom_min
                .get(signature)
                .map(|bottom_cost| top_cost + bottom_cost)
        })
        .min();
    let mut results = BTreeMap::new();
    for &budget in &manifest.join_budgets {
        let (tested, connected, best) = join(&top, &bottom, budget, manifest.target_n);
        results.insert(
            budget,
            serde_json::json!({
                "tested": tested,
                "connected": connected,
                "best_components": best,
                "conclusion": if connected > 0 { "SAT" } else { "UNSAT_IN_LANGUAGE" },
            }),
        );
    }
    println!(
        "{}",
        serde_json::to_string_pretty(&serde_json::json!({
            "schema": "grid-graphs.residue-two-self-renewal-result.v1",
            "top_states": top.len(),
            "bottom_states": bottom.len(),
            "beam": beam,
            "common_signatures": common_signatures,
            "minimum_join_cost": minimum_join_cost,
            "budgets": results,
            "elapsed_seconds": started.elapsed().as_secs_f64(),
        }))
        .unwrap()
    );
    Ok(())
}

fn main() {
    let mut args = env::args().skip(1);
    let path = args.next().unwrap_or_else(|| {
        eprintln!("usage: search_residue_two_self_renewal MANIFEST.json [--beam N]");
        process::exit(2);
    });
    let beam = match args.next().as_deref() {
        None => None,
        Some("--beam") => Some(
            args.next()
                .unwrap_or_else(|| {
                    eprintln!("--beam requires a positive integer");
                    process::exit(2);
                })
                .parse()
                .unwrap_or_else(|_| {
                    eprintln!("--beam requires a positive integer");
                    process::exit(2);
                }),
        ),
        Some(other) => {
            eprintln!("unknown argument: {other}");
            process::exit(2);
        }
    };
    if beam == Some(0) || args.next().is_some() {
        eprintln!("invalid trailing arguments or zero beam");
        process::exit(2);
    }
    if let Err(error) = run(&path, beam) {
        eprintln!("error: {error}");
        process::exit(2);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn partition_packing_rejects_noncanonical_labels() {
        assert!(pack_partition(&[0, 2], 2).is_err());
        assert_eq!(pack_partition(&[0, 1, 1], 3).unwrap(), 1 << 5 | 1 << 10);
    }

    #[test]
    fn full_first_row_connects_every_frontier_face_to_out() {
        let n = 6;
        let state = State {
            labels: 0,
            previous_u: 0,
            cost: 0,
            cycles: 0,
        };
        let outgoing = advance_row(state, (1 << n) - 1, 0, n).unwrap();
        assert_eq!(component_count(outgoing.labels, n), 1);
    }
}
