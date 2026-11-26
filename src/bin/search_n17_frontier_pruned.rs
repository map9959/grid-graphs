//! Exact fixed-cardinality frontier DP for dual connectivity induced by U vertices.
//!
//! Grid vertices are streamed in row-major order.  When `(r, c)` is chosen, the
//! primal edges to its left and upper neighbors become known.  Their dual edges
//! are present exactly when both primal endpoints are in U.

use std::env;
use std::fmt::Write as _;
use std::fs;
use std::hash::BuildHasherDefault;
use std::io::{BufReader, BufWriter, Read, Write};
use std::path::{Path, PathBuf};
use std::process;
use std::time::{Duration, Instant};

use fxhash::FxHasher;
use grid_graphs::exact_centered_square::{
    CenteredSquareMonitor, StreamingSquare, StreamingSquareState,
};
use hashbrown::HashMap;

#[cfg(test)]
#[path = "../frontier_primal_tests.rs"]
mod independent_primal_tests;

const MAX_N: usize = 17;
const LABEL_BITS: usize = 5;
const MAX_BAG: usize = 128 / LABEL_BITS;
const MAX_WORK_NODES: usize = MAX_N + 2;
const LABEL_REGION_BITS: usize = MAX_N * LABEL_BITS;
const ROW_SHIFT: usize = LABEL_REGION_BITS;
const LABEL_MASK: u128 = (1u128 << LABEL_REGION_BITS) - 1;
const ROW_MASK: u128 = (1u128 << MAX_N) - 1;
const CHECKPOINT_MAGIC: &[u8; 8] = b"GGFDP002";
const CHECKPOINT_HEADER_BYTES: u64 = 44;
const CHECKPOINT_RECORD_BYTES: u64 = 18;
const CHECKPOINT_TRAILER_BYTES: u64 = 8;

type FastMap<K, V> = HashMap<K, V, BuildHasherDefault<FxHasher>>;

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
enum PruningMode {
    #[default]
    None,
    Mirror,
    Geometry,
    Closure,
    All,
}

impl PruningMode {
    fn parse(value: &str) -> Result<Self, String> {
        match value {
            "none" => Ok(Self::None),
            "mirror" => Ok(Self::Mirror),
            "geometry" => Ok(Self::Geometry),
            "closure" => Ok(Self::Closure),
            "all" => Ok(Self::All),
            _ => Err(format!(
                "invalid --pruning value {value:?}; expected none|mirror|geometry|closure|all"
            )),
        }
    }

    fn mirror(self) -> bool {
        matches!(self, Self::Mirror | Self::All)
    }

    fn geometry(self) -> bool {
        matches!(self, Self::Geometry | Self::All)
    }

    fn closure(self) -> bool {
        matches!(self, Self::Closure | Self::All)
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct State(u128);

impl State {
    fn new(labels: u128, row_u: u32) -> Self {
        debug_assert_eq!(labels & !LABEL_MASK, 0);
        debug_assert!(row_u < 1 << MAX_N);
        Self(labels | ((row_u as u128) << ROW_SHIFT))
    }

    fn labels(self) -> u128 {
        self.0 & LABEL_MASK
    }

    // Columns already overwritten hold the current row; the rest hold the prior row.
    fn row_u(self) -> u32 {
        ((self.0 >> ROW_SHIFT) & ROW_MASK) as u32
    }
}

#[derive(Clone, Copy)]
enum Neighbor {
    Left,
    Up,
}

#[derive(Clone, Copy)]
struct DualEdge {
    a: usize,
    b: usize,
    a_slot: usize,
    b_slot: usize,
    neighbor: Neighbor,
}

struct Step {
    row: usize,
    col: usize,
    before: Vec<usize>,
    nodes: Vec<usize>,
    after_indices: Vec<usize>,
    introduced_before: usize,
    introduced_nodes: usize,
    edges: Vec<DualEdge>,
}

#[derive(Debug)]
struct SearchStats {
    feasible: bool,
    minimum_u: Option<u16>,
    peak_states: usize,
    generated_transitions: u64,
    state_counts: Vec<usize>,
    state_count_start: usize,
    elapsed: Duration,
    peak_rss_kib: Option<u64>,
    mirror_merges: u64,
    geometry_prunes: u64,
    closure_prunes: u64,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct GrammarHistoryState {
    frontier: State,
    violated: bool,
}

#[derive(Clone, Copy)]
struct GrammarTrace {
    cost: u16,
    row_parent: GrammarHistoryState,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
enum GrammarViolationKind {
    #[default]
    Combined,
    SupportHole,
    ConcurrentCarriers,
    LocalMotif,
    FaceCut,
}

impl GrammarViolationKind {
    fn parse(value: &str) -> Result<Self, String> {
        match value {
            "combined" => Ok(Self::Combined),
            "support-hole" => Ok(Self::SupportHole),
            "concurrent-carriers" => Ok(Self::ConcurrentCarriers),
            "local-motif" => Ok(Self::LocalMotif),
            "face-cut" => Ok(Self::FaceCut),
            _ => Err(format!(
                "invalid grammar violation kind {value:?}; expected combined|support-hole|concurrent-carriers|local-motif|face-cut"
            )),
        }
    }
}

#[derive(Clone, Copy, Default)]
struct GrammarDefects {
    support_hole: bool,
    concurrent_carriers: bool,
    local_motif: bool,
    face_cut: bool,
}

impl GrammarDefects {
    fn has(self, kind: GrammarViolationKind) -> bool {
        match kind {
            GrammarViolationKind::Combined => {
                self.support_hole || self.concurrent_carriers || self.local_motif
            }
            GrammarViolationKind::SupportHole => self.support_hole,
            GrammarViolationKind::ConcurrentCarriers => self.concurrent_carriers,
            GrammarViolationKind::LocalMotif => self.local_motif,
            GrammarViolationKind::FaceCut => self.face_cut,
        }
    }
}

#[derive(Debug)]
struct GrammarQueryStats {
    minimum_good_u: Option<u16>,
    minimum_bad_u: Option<u16>,
    peak_states: usize,
    generated_transitions: u64,
    elapsed: Duration,
    bad_witness_rows: Option<Vec<u32>>,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum CenteredProduct {
    Streaming(u32),
    Profile(u8),
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct CenteredProductState {
    frontier: State,
    u_count: u16,
    centered: CenteredProduct,
}

#[derive(Clone, Copy)]
struct CenteredProductTrace {
    row_parent: u32,
}

#[derive(Clone, Copy)]
struct CenteredThresholds {
    repeated_components: usize,
    maximum_cyclic_runs: usize,
    compressed_runs: usize,
}

struct ThresholdAutomaton {
    initial: u32,
    transitions: Vec<Vec<[u32; 2]>>,
    outputs: Vec<u8>,
    exact_layer_counts: Vec<usize>,
    quotient_layer_counts: Vec<usize>,
}

impl ThresholdAutomaton {
    fn build(side: usize, thresholds: CenteredThresholds, progress: bool) -> Result<Self, String> {
        let stream = StreamingSquare::new(side)?;
        let mut states = vec![(stream.initial_state(), 0u16)];
        let mut exact_transitions = Vec::with_capacity(side * side);
        let mut exact_layer_counts = vec![1];

        for position in 0..side * side {
            let col = position % side;
            let mut next_states = Vec::new();
            let mut next_ids: FastMap<(StreamingSquareState, u16), u32> =
                FastMap::with_hasher(BuildHasherDefault::default());
            let mut layer = Vec::with_capacity(states.len());
            for &(state, row_u) in &states {
                let mut successors = [0; 2];
                for (chosen_index, chosen) in [false, true].into_iter().enumerate() {
                    let next_state = stream.advance(state, position, chosen, row_u)?;
                    let mut next_row_u = row_u;
                    if chosen {
                        next_row_u |= 1 << col;
                    } else {
                        next_row_u &= !(1 << col);
                    }
                    let next_id = *next_ids.entry((next_state, next_row_u)).or_insert_with(|| {
                        let id = next_states.len() as u32;
                        next_states.push((next_state, next_row_u));
                        id
                    });
                    successors[chosen_index] = next_id;
                }
                layer.push(successors);
            }
            exact_transitions.push(layer);
            states = next_states;
            exact_layer_counts.push(states.len());
            if progress {
                eprintln!(
                    "threshold_automaton phase=forward position={}/{} exact_states={}",
                    position + 1,
                    side * side,
                    states.len()
                );
            }
        }

        let mut output_to_class = [u32::MAX; 8];
        let mut outputs = Vec::new();
        let mut next_classes = Vec::with_capacity(states.len());
        for (state, _) in &states {
            let flags = centered_summary_violation_flags(&stream.summary(state), thresholds);
            let class = if output_to_class[flags as usize] == u32::MAX {
                let class = outputs.len() as u32;
                output_to_class[flags as usize] = class;
                outputs.push(flags);
                class
            } else {
                output_to_class[flags as usize]
            };
            next_classes.push(class);
        }

        let mut transitions = vec![Vec::new(); side * side];
        let mut quotient_layer_counts = vec![0; side * side + 1];
        quotient_layer_counts[side * side] = outputs.len();
        for position in (0..side * side).rev() {
            let mut signature_ids: FastMap<[u32; 2], u32> =
                FastMap::with_hasher(BuildHasherDefault::default());
            let mut classes = Vec::with_capacity(exact_transitions[position].len());
            let mut class_transitions = Vec::new();
            for successors in &exact_transitions[position] {
                let signature = [
                    next_classes[successors[0] as usize],
                    next_classes[successors[1] as usize],
                ];
                let class = *signature_ids.entry(signature).or_insert_with(|| {
                    let id = class_transitions.len() as u32;
                    class_transitions.push(signature);
                    id
                });
                classes.push(class);
            }
            quotient_layer_counts[position] = class_transitions.len();
            transitions[position] = class_transitions;
            next_classes = classes;
            if progress {
                eprintln!(
                    "threshold_automaton phase=backward position={position} quotient_states={}",
                    quotient_layer_counts[position]
                );
            }
        }
        Ok(Self {
            initial: next_classes[0],
            transitions,
            outputs,
            exact_layer_counts,
            quotient_layer_counts,
        })
    }
}

#[derive(Debug)]
struct CenteredProductStats {
    connected: bool,
    violation_flags: u8,
    peak_states: usize,
    generated_transitions: u64,
    equivalent_merges: u64,
    state_counts: Vec<usize>,
    elapsed: Duration,
    witness_rows: Option<Vec<u32>>,
}

#[derive(Default)]
struct SearchOptions<'a> {
    checkpoint: Option<&'a Path>,
    resume: bool,
    progress: bool,
    pruning: PruningMode,
    dump_step: Option<usize>,
    dump_out: Option<&'a Path>,
}

struct Checkpoint {
    completed_steps: usize,
    peak_states: usize,
    generated_transitions: u64,
    states: FastMap<State, u16>,
}

#[derive(Debug)]
struct BidirectionalStats {
    minimum_u: Option<u16>,
    meeting_step: usize,
    forward_state_counts: Vec<usize>,
    backward_state_counts: Vec<(usize, usize)>,
    reverse_candidates: u64,
}

fn face(n: usize, row: usize, col: usize) -> usize {
    row * (n - 1) + col
}

fn steps(n: usize) -> Result<Vec<Step>, String> {
    let face_count = (n - 1) * (n - 1);
    let out = face_count;
    let mut edge_batches = vec![Vec::new(); n * n];

    for row in 0..n {
        for col in 0..n {
            let batch = &mut edge_batches[row * n + col];
            if col > 0 {
                batch.push(DualEdge {
                    a: if row == 0 {
                        out
                    } else {
                        face(n, row - 1, col - 1)
                    },
                    b: if row + 1 == n {
                        out
                    } else {
                        face(n, row, col - 1)
                    },
                    a_slot: 0,
                    b_slot: 0,
                    neighbor: Neighbor::Left,
                });
            }
            if row > 0 {
                batch.push(DualEdge {
                    a: if col == 0 {
                        out
                    } else {
                        face(n, row - 1, col - 1)
                    },
                    b: if col + 1 == n {
                        out
                    } else {
                        face(n, row - 1, col)
                    },
                    a_slot: 0,
                    b_slot: 0,
                    neighbor: Neighbor::Up,
                });
            }
        }
    }

    let mut first = vec![usize::MAX; face_count];
    let mut last = vec![0; face_count];
    for (at, batch) in edge_batches.iter().enumerate() {
        for edge in batch {
            for node in [edge.a, edge.b] {
                if node != out {
                    first[node] = first[node].min(at);
                    last[node] = last[node].max(at);
                }
            }
        }
    }

    let bag_before = |at: usize| {
        let mut bag = vec![out];
        bag.extend((0..face_count).filter(|&node| first[node] < at && last[node] >= at));
        bag
    };
    let bag_after = |at: usize| {
        let mut bag = vec![out];
        bag.extend((0..face_count).filter(|&node| first[node] <= at && last[node] > at));
        bag
    };

    let mut result = Vec::with_capacity(n * n);
    for (at, mut edges) in edge_batches.into_iter().enumerate() {
        let before = bag_before(at);
        let after = bag_after(at);
        if before.len().max(after.len()) > MAX_BAG {
            return Err(format!(
                "frontier requires {} slots, packed representation supports {MAX_BAG}",
                before.len().max(after.len())
            ));
        }
        let mut nodes = before.clone();
        for edge in &edges {
            for node in [edge.a, edge.b] {
                if !nodes.contains(&node) {
                    nodes.push(node);
                }
            }
        }
        if nodes.len() > MAX_WORK_NODES {
            return Err(format!(
                "transition requires {} work nodes, supports {MAX_WORK_NODES}",
                nodes.len()
            ));
        }
        for edge in &mut edges {
            edge.a_slot = nodes.iter().position(|&node| node == edge.a).unwrap();
            edge.b_slot = nodes.iter().position(|&node| node == edge.b).unwrap();
        }
        let after_indices = after
            .iter()
            .map(|node| {
                nodes
                    .iter()
                    .position(|candidate| candidate == node)
                    .unwrap()
            })
            .collect();
        let introduced_before = 1 + first.iter().filter(|&&first_at| first_at < at).count();
        let introduced_nodes = 1 + first.iter().filter(|&&first_at| first_at <= at).count();
        result.push(Step {
            row: at / n,
            col: at % n,
            before,
            nodes,
            after_indices,
            introduced_before,
            introduced_nodes,
            edges,
        });
    }
    Ok(result)
}

fn label_at(labels: u128, slot: usize) -> usize {
    ((labels >> (LABEL_BITS * slot)) & 31) as usize
}

fn component_count(labels: u128, slots: usize) -> usize {
    (0..slots)
        .map(|slot| label_at(labels, slot))
        .max()
        .map_or(0, |label| label + 1)
}

fn root(parent: &mut [usize], mut node: usize) -> usize {
    while parent[node] != node {
        parent[node] = parent[parent[node]];
        node = parent[node];
    }
    node
}

fn join(parent: &mut [usize], a: usize, b: usize) {
    let a = root(parent, a);
    let b = root(parent, b);
    if a != b {
        parent[b] = a;
    }
}

fn canonicalize_labels(labels: impl IntoIterator<Item = usize>) -> u128 {
    let mut old_labels = [usize::MAX; MAX_BAG];
    let mut old_count = 0;
    let mut packed = 0u128;
    for (slot, label) in labels.into_iter().enumerate() {
        let canonical = match old_labels[..old_count]
            .iter()
            .position(|&seen| seen == label)
        {
            Some(existing) => existing,
            None => {
                old_labels[old_count] = label;
                old_count += 1;
                old_count - 1
            }
        };
        packed |= (canonical as u128) << (LABEL_BITS * slot);
    }
    packed
}

fn reflected_row_boundary_state(state: State, step: &Step, n: usize) -> State {
    let side = n - 1;
    let out = side * side;
    let after_nodes: Vec<_> = step
        .after_indices
        .iter()
        .map(|&index| step.nodes[index])
        .collect();
    let reflected_labels = after_nodes.iter().map(|&node| {
        let reflected = if node == out {
            out
        } else {
            let row = node / side;
            let col = node % side;
            row * side + (side - 1 - col)
        };
        let source = after_nodes
            .iter()
            .position(|&candidate| candidate == reflected)
            .expect("row-boundary bag must be reflection invariant");
        label_at(state.labels(), source)
    });
    let reversed_row = state.row_u().reverse_bits() >> (u32::BITS as usize - n);
    State::new(canonicalize_labels(reflected_labels), reversed_row)
}

#[derive(Clone)]
struct ClosureProfile {
    component_by_slot: [u8; MAX_BAG],
    component_count: usize,
    out_component: usize,
    all_components_represented: bool,
}

fn closure_profile(
    n: usize,
    schedule: &[Step],
    completed: usize,
    boundary_step: &Step,
    row_u: u32,
) -> ClosureProfile {
    let dual_nodes = (n - 1) * (n - 1) + 1;
    let out = dual_nodes - 1;
    let mut parent: Vec<usize> = (0..dual_nodes).collect();
    let mut relevant = vec![false; dual_nodes];
    let after_nodes: Vec<_> = boundary_step
        .after_indices
        .iter()
        .map(|&index| boundary_step.nodes[index])
        .collect();
    for &node in &after_nodes {
        relevant[node] = true;
    }
    for step in &schedule[completed..] {
        for edge in &step.edges {
            relevant[edge.a] = true;
            relevant[edge.b] = true;
            let possible = match edge.neighbor {
                Neighbor::Left => true,
                Neighbor::Up if step.row == boundary_step.row + 1 => row_u & (1 << step.col) != 0,
                Neighbor::Up => true,
            };
            if possible {
                join(&mut parent, edge.a, edge.b);
            }
        }
    }

    let mut roots = Vec::new();
    for node in 0..dual_nodes {
        if relevant[node] {
            let component = root(&mut parent, node);
            if !roots.contains(&component) {
                roots.push(component);
            }
        }
    }
    let mut component_by_slot = [0u8; MAX_BAG];
    let mut represented = vec![false; roots.len()];
    for (slot, &node) in after_nodes.iter().enumerate() {
        let component = root(&mut parent, node);
        let id = roots
            .iter()
            .position(|&candidate| candidate == component)
            .unwrap();
        component_by_slot[slot] = id as u8;
        represented[id] = true;
    }
    let out_root = root(&mut parent, out);
    ClosureProfile {
        component_by_slot,
        component_count: roots.len(),
        out_component: roots
            .iter()
            .position(|&candidate| candidate == out_root)
            .unwrap(),
        all_components_represented: represented.into_iter().all(|value| value),
    }
}

fn closure_can_connect(state: State, slots: usize, profile: &ClosureProfile) -> bool {
    if !profile.all_components_represented || profile.component_count > MAX_BAG {
        return false;
    }
    let mut parent = [0usize; MAX_BAG];
    for (index, value) in parent.iter_mut().enumerate().take(profile.component_count) {
        *value = index;
    }
    for left in 0..slots {
        for right in 0..left {
            if label_at(state.labels(), left) == label_at(state.labels(), right) {
                join(
                    &mut parent,
                    profile.component_by_slot[left] as usize,
                    profile.component_by_slot[right] as usize,
                );
            }
        }
    }
    let out_root = root(&mut parent, profile.out_component);
    (0..profile.component_count).all(|component| root(&mut parent, component) == out_root)
}

fn advance_labels(labels: u128, step: &Step, active_edges: u8) -> Option<u128> {
    let mut parent = [0usize; MAX_WORK_NODES];
    for (index, value) in parent.iter_mut().enumerate().take(step.nodes.len()) {
        *value = index;
    }

    for i in 0..step.before.len() {
        for j in 0..i {
            if label_at(labels, i) == label_at(labels, j) {
                join(&mut parent, i, j);
            }
        }
    }
    for (edge_index, edge) in step.edges.iter().enumerate() {
        if active_edges & (1 << edge_index) != 0 {
            join(&mut parent, edge.a_slot, edge.b_slot);
        }
    }

    let mut represented = [false; MAX_WORK_NODES];
    for &index in &step.after_indices {
        let component = root(&mut parent, index);
        represented[component] = true;
    }
    for index in 0..step.nodes.len() {
        let component = root(&mut parent, index);
        if !represented[component] {
            return None;
        }
    }

    let mut next_labels = 0u128;
    let mut component_labels = [usize::MAX; MAX_BAG];
    let mut component_count = 0;
    for (slot, &index) in step.after_indices.iter().enumerate() {
        let component = root(&mut parent, index);
        let canonical = match component_labels[..component_count]
            .iter()
            .position(|&seen| seen == component)
        {
            Some(label) => label,
            None => {
                component_labels[component_count] = component;
                component_count += 1;
                component_count - 1
            }
        };
        next_labels |= (canonical as u128) << (LABEL_BITS * slot);
    }

    Some(next_labels)
}

fn advance(state: State, step: &Step, chosen: bool) -> Option<State> {
    let row_u = state.row_u();
    let mut active_edges = 0;
    if chosen {
        for (edge_index, edge) in step.edges.iter().enumerate() {
            let neighbor_u = match edge.neighbor {
                Neighbor::Left => step.col > 0 && row_u & (1 << (step.col - 1)) != 0,
                Neighbor::Up => step.row > 0 && row_u & (1 << step.col) != 0,
            };
            if neighbor_u {
                active_edges |= 1 << edge_index;
            }
        }
    }
    let labels = advance_labels(state.labels(), step, active_edges)?;

    let mut row_u = row_u;
    if chosen {
        row_u |= 1 << step.col;
    } else {
        row_u &= !(1 << step.col);
    }
    Some(State::new(labels, row_u))
}

fn reverse_predecessors(post: State, step: &Step) -> Vec<State> {
    let chosen = post.row_u() & (1 << step.col) != 0;
    let post_components = component_count(post.labels(), step.after_indices.len());
    let introduced = step.nodes.len() - step.before.len();
    let mut result = Vec::new();

    for previous_up in [false, true] {
        let mut row_u = post.row_u();
        if previous_up {
            row_u |= 1 << step.col;
        } else {
            row_u &= !(1 << step.col);
        }

        let mut active_edges = 0u8;
        if chosen {
            for (edge_index, edge) in step.edges.iter().enumerate() {
                let neighbor_u = match edge.neighbor {
                    Neighbor::Left => step.col > 0 && row_u & (1 << (step.col - 1)) != 0,
                    Neighbor::Up => step.row > 0 && row_u & (1 << step.col) != 0,
                };
                if neighbor_u {
                    active_edges |= 1 << edge_index;
                }
            }
        }

        let active_count = active_edges.count_ones() as usize;
        let Some(max_before_components) = post_components
            .checked_add(active_count)
            .and_then(|count| count.checked_sub(introduced))
        else {
            continue;
        };
        if max_before_components == 0 && !step.before.is_empty() {
            continue;
        }

        let mut survivor_labels = vec![None; step.before.len()];
        for (post_slot, &work_index) in step.after_indices.iter().enumerate() {
            if work_index < step.before.len() {
                survivor_labels[work_index] = Some(label_at(post.labels(), post_slot));
            }
        }

        fn enumerate(
            slot: usize,
            used: usize,
            packed: u128,
            block_post_labels: &mut [Option<usize>; MAX_BAG],
            survivor_labels: &[Option<usize>],
            max_components: usize,
            row_u: u32,
            chosen: bool,
            post: State,
            step: &Step,
            result: &mut Vec<State>,
        ) {
            if slot == step.before.len() {
                let candidate = State::new(packed, row_u);
                if advance(candidate, step, chosen) == Some(post) {
                    result.push(candidate);
                }
                return;
            }

            let upper = used.min(max_components.saturating_sub(1));
            for label in 0..=upper {
                let is_new = label == used;
                let next_used = used + usize::from(is_new);
                if next_used > max_components {
                    continue;
                }
                let survivor = survivor_labels[slot];
                if let (Some(existing), Some(current)) = (block_post_labels[label], survivor) {
                    if existing != current {
                        continue;
                    }
                }
                let old = block_post_labels[label];
                if old.is_none() {
                    block_post_labels[label] = survivor;
                }
                enumerate(
                    slot + 1,
                    next_used,
                    packed | ((label as u128) << (LABEL_BITS * slot)),
                    block_post_labels,
                    survivor_labels,
                    max_components,
                    row_u,
                    chosen,
                    post,
                    step,
                    result,
                );
                block_post_labels[label] = old;
            }
        }

        enumerate(
            0,
            0,
            0,
            &mut [None; MAX_BAG],
            &survivor_labels,
            max_before_components,
            row_u,
            chosen,
            post,
            step,
            &mut result,
        );
    }
    result.sort_unstable_by_key(|state| state.0);
    result.dedup();
    result
}

fn bidirectional_search(
    n: usize,
    target: usize,
    meeting_step: usize,
) -> Result<BidirectionalStats, String> {
    if n == 0 || n > MAX_N {
        return Err(format!("n must be in 1..={MAX_N}"));
    }
    if target > n * n {
        return Err(format!("U count cannot exceed {}", n * n));
    }
    let schedule = steps(n)?;
    if meeting_step > schedule.len() {
        return Err(format!("meeting step must be at most {}", schedule.len()));
    }

    let mut backward: FastMap<State, u16> = FastMap::with_hasher(BuildHasherDefault::default());
    for row_u in 0..1u32 << n {
        backward.insert(State::new(0, row_u), 0);
    }
    let mut backward_state_counts = vec![(schedule.len(), backward.len())];
    let mut reverse_candidates = 0u64;
    for (at, step) in schedule[meeting_step..].iter().enumerate().rev() {
        let mut previous: FastMap<State, u16> = FastMap::with_hasher(BuildHasherDefault::default());
        for (&post, &suffix_cost) in &backward {
            let chosen_cost = u16::from(post.row_u() & (1 << step.col) != 0);
            for predecessor in reverse_predecessors(post, step) {
                reverse_candidates += 1;
                let cost = suffix_cost + chosen_cost;
                if cost as usize > target {
                    continue;
                }
                let components = component_count(predecessor.labels(), step.before.len());
                let prefix_rank = step.introduced_before - components;
                let minimum_prefix_u = prefix_rank
                    .div_ceil(2)
                    .max(predecessor.row_u().count_ones() as usize);
                if cost as usize + minimum_prefix_u > target {
                    continue;
                }
                previous
                    .entry(predecessor)
                    .and_modify(|existing| *existing = (*existing).min(cost))
                    .or_insert(cost);
            }
        }
        backward = previous;
        backward_state_counts.push((meeting_step + at, backward.len()));
    }

    let mut forward: FastMap<State, u16> = FastMap::with_hasher(BuildHasherDefault::default());
    forward.insert(State::new(0, 0), 0);
    let mut forward_state_counts = vec![1];
    let dual_nodes = (n - 1) * (n - 1) + 1;
    for step in &schedule[..meeting_step] {
        let entries: Vec<(State, u16)> = forward.into_iter().collect();
        let (next, _) = extend_chunk(&entries, step, target, dual_nodes);
        forward = next;
        forward_state_counts.push(forward.len());
    }

    let minimum_u = forward
        .iter()
        .filter_map(|(state, prefix)| backward.get(state).map(|suffix| prefix + suffix))
        .filter(|&cost| cost as usize <= target)
        .min();
    Ok(BidirectionalStats {
        minimum_u,
        meeting_step,
        forward_state_counts,
        backward_state_counts,
        reverse_candidates,
    })
}

fn extend_chunk(
    entries: &[(State, u16)],
    step: &Step,
    target: usize,
    dual_nodes: usize,
) -> (FastMap<State, u16>, u64) {
    let mut next: FastMap<State, u16> = FastMap::with_capacity_and_hasher(
        entries.len().saturating_mul(2),
        BuildHasherDefault::default(),
    );
    let mut transition_cache: FastMap<(u128, u8), Option<u128>> =
        FastMap::with_hasher(BuildHasherDefault::default());
    let mut generated = 0;
    for &(state, cost) in entries {
        let row_u = state.row_u();
        for chosen in [false, true] {
            let next_cost = cost + u16::from(chosen);
            if next_cost as usize > target {
                continue;
            }
            generated += 1;
            let mut active_edges = 0;
            if chosen {
                for (edge_index, edge) in step.edges.iter().enumerate() {
                    let neighbor_u = match edge.neighbor {
                        Neighbor::Left => step.col > 0 && row_u & (1 << (step.col - 1)) != 0,
                        Neighbor::Up => step.row > 0 && row_u & (1 << step.col) != 0,
                    };
                    if neighbor_u {
                        active_edges |= 1 << edge_index;
                    }
                }
            }
            let next_labels = *transition_cache
                .entry((state.labels(), active_edges))
                .or_insert_with(|| advance_labels(state.labels(), step, active_edges));
            if let Some(labels) = next_labels {
                let components = component_count(labels, step.after_indices.len());
                let current_rank = step.introduced_nodes - components;
                let rank_deficit = (dual_nodes - 1) - current_rank;
                let minimum_additional_u = rank_deficit.div_ceil(2);
                if next_cost as usize + minimum_additional_u > target {
                    continue;
                }
                let mut next_row_u = row_u;
                if chosen {
                    next_row_u |= 1 << step.col;
                } else {
                    next_row_u &= !(1 << step.col);
                }
                let candidate = State::new(labels, next_row_u);
                next.entry(candidate)
                    .and_modify(|existing| *existing = (*existing).min(next_cost))
                    .or_insert(next_cost);
            }
        }
    }
    (next, generated)
}

fn extend_grammar_chunk(
    entries: &[(GrammarHistoryState, GrammarTrace)],
    step: &Step,
    target: usize,
    dual_nodes: usize,
) -> (FastMap<GrammarHistoryState, GrammarTrace>, u64) {
    let mut next: FastMap<GrammarHistoryState, GrammarTrace> = FastMap::with_capacity_and_hasher(
        entries.len().saturating_mul(2),
        BuildHasherDefault::default(),
    );
    let mut transition_cache: FastMap<(u128, u8), Option<u128>> =
        FastMap::with_hasher(BuildHasherDefault::default());
    let mut generated = 0;
    for &(history, trace) in entries {
        let state = history.frontier;
        let row_u = state.row_u();
        for chosen in [false, true] {
            let next_cost = trace.cost + u16::from(chosen);
            if next_cost as usize > target {
                continue;
            }
            generated += 1;
            let mut active_edges = 0;
            if chosen {
                for (edge_index, edge) in step.edges.iter().enumerate() {
                    let neighbor_u = match edge.neighbor {
                        Neighbor::Left => step.col > 0 && row_u & (1 << (step.col - 1)) != 0,
                        Neighbor::Up => step.row > 0 && row_u & (1 << step.col) != 0,
                    };
                    if neighbor_u {
                        active_edges |= 1 << edge_index;
                    }
                }
            }
            let next_labels = *transition_cache
                .entry((state.labels(), active_edges))
                .or_insert_with(|| advance_labels(state.labels(), step, active_edges));
            if let Some(labels) = next_labels {
                let components = component_count(labels, step.after_indices.len());
                let current_rank = step.introduced_nodes - components;
                let rank_deficit = (dual_nodes - 1) - current_rank;
                let minimum_additional_u = rank_deficit.div_ceil(2);
                if next_cost as usize + minimum_additional_u > target {
                    continue;
                }
                let mut next_row_u = row_u;
                if chosen {
                    next_row_u |= 1 << step.col;
                } else {
                    next_row_u &= !(1 << step.col);
                }
                let candidate = GrammarHistoryState {
                    frontier: State::new(labels, next_row_u),
                    violated: history.violated,
                };
                let candidate_trace = GrammarTrace {
                    cost: next_cost,
                    row_parent: trace.row_parent,
                };
                next.entry(candidate)
                    .and_modify(|existing| {
                        if (
                            candidate_trace.cost,
                            candidate_trace.row_parent.frontier.0,
                            candidate_trace.row_parent.violated,
                        ) < (
                            existing.cost,
                            existing.row_parent.frontier.0,
                            existing.row_parent.violated,
                        ) {
                            *existing = candidate_trace;
                        }
                    })
                    .or_insert(candidate_trace);
            }
        }
    }
    (next, generated)
}

fn residue_two_grammar_defects(state: State, slots: usize, n: usize) -> GrammarDefects {
    if n < 5 || n % 3 != 2 {
        return GrammarDefects {
            support_hole: true,
            ..GrammarDefects::default()
        };
    }
    if slots == 1 {
        return GrammarDefects::default();
    }
    if slots != n {
        return GrammarDefects {
            support_hole: true,
            ..GrammarDefects::default()
        };
    }
    let out = label_at(state.labels(), 0);
    let packet_count = (n - 2) / 3;
    let mut supports: FastMap<usize, u64> = FastMap::with_hasher(BuildHasherDefault::default());
    for face in 0..n - 1 {
        let component = label_at(state.labels(), face + 1);
        if component == out {
            continue;
        }
        let group = if face == 0 { 0 } else { (face + 2) / 3 };
        *supports.entry(component).or_insert(0) |= 1 << group;
    }
    let support_hole = supports.values().any(|support| {
        let first = support.trailing_zeros() as usize;
        let last = (u64::BITS - 1 - support.leading_zeros()) as usize;
        let interval = ((1u64 << (last - first + 1)) - 1) << first;
        *support != interval
    });
    let concurrent_carriers = (0..packet_count).any(|cut| {
        supports
            .values()
            .filter(|support| {
                let first = support.trailing_zeros() as usize;
                let last = (u64::BITS - 1 - support.leading_zeros()) as usize;
                first <= cut && cut < last
            })
            .count()
            > 1
    });
    let local_motif = (0..packet_count).any(|packet| {
        let first = label_at(state.labels(), 2 + 3 * packet);
        let middle = label_at(state.labels(), 3 + 3 * packet);
        let last = label_at(state.labels(), 4 + 3 * packet);
        let forbidden_010 = first == out && middle != out && last == out;
        let forbidden_101 = first != out && middle == out && last == first;
        let forbidden_121 = first != out && middle != out && middle != first && last == first;
        forbidden_010 || forbidden_101 || forbidden_121
    });
    let mut face_hulls: FastMap<usize, (usize, usize)> =
        FastMap::with_hasher(BuildHasherDefault::default());
    for face in 0..n - 1 {
        let component = label_at(state.labels(), face + 1);
        if component != out {
            face_hulls
                .entry(component)
                .and_modify(|hull| hull.1 = face)
                .or_insert((face, face));
        }
    }
    let face_cut = (0..n - 2).any(|cut| {
        face_hulls
            .values()
            .filter(|(first, last)| *first <= cut && cut < *last)
            .count()
            > 1
    });
    GrammarDefects {
        support_hole,
        concurrent_carriers,
        local_motif,
        face_cut,
    }
}

fn mark_grammar_violations(
    states: FastMap<GrammarHistoryState, GrammarTrace>,
    n: usize,
    slots: usize,
    kind: GrammarViolationKind,
) -> FastMap<GrammarHistoryState, GrammarTrace> {
    let mut marked: FastMap<GrammarHistoryState, GrammarTrace> =
        FastMap::with_capacity_and_hasher(states.len(), BuildHasherDefault::default());
    for (history, trace) in states {
        let candidate = GrammarHistoryState {
            frontier: history.frontier,
            violated: history.violated
                || residue_two_grammar_defects(history.frontier, slots, n).has(kind),
        };
        marked
            .entry(candidate)
            .and_modify(|existing| {
                if (
                    trace.cost,
                    trace.row_parent.frontier.0,
                    trace.row_parent.violated,
                ) < (
                    existing.cost,
                    existing.row_parent.frontier.0,
                    existing.row_parent.violated,
                ) {
                    *existing = trace;
                }
            })
            .or_insert(trace);
    }
    marked
}

fn grammar_violation_search(
    n: usize,
    target: usize,
    progress: bool,
    recover_witness: bool,
    kind: GrammarViolationKind,
) -> Result<GrammarQueryStats, String> {
    if n < 5 || n > MAX_N || n % 3 != 2 {
        return Err(format!(
            "grammar violation query requires n=3k+2 in 5..={MAX_N}"
        ));
    }
    if target > n * n {
        return Err(format!("U count cannot exceed {}", n * n));
    }
    let started = Instant::now();
    let schedule = steps(n)?;
    let dual_nodes = (n - 1) * (n - 1) + 1;
    let mut states = FastMap::with_hasher(BuildHasherDefault::default());
    let initial = GrammarHistoryState {
        frontier: State::new(0, 0),
        violated: false,
    };
    states.insert(
        initial,
        GrammarTrace {
            cost: 0,
            row_parent: initial,
        },
    );
    let mut peak_states = 1;
    let mut generated_transitions = 0;
    let mut row_parents: Option<Vec<FastMap<GrammarHistoryState, (GrammarHistoryState, u32)>>> =
        recover_witness.then(Vec::new);
    for (index, step) in schedule.iter().enumerate() {
        let step_started = Instant::now();
        let entries: Vec<_> = states.into_iter().collect();
        let (next, generated) = extend_grammar_chunk(&entries, step, target, dual_nodes);
        generated_transitions += generated;
        states = next;
        let completed = index + 1;
        if completed % n == 0 {
            states = mark_grammar_violations(states, n, step.after_indices.len(), kind);
            if let Some(layers) = &mut row_parents {
                layers.push(
                    states
                        .iter()
                        .map(|(&state, trace)| (state, (trace.row_parent, state.frontier.row_u())))
                        .collect(),
                );
            }
            for (state, trace) in &mut states {
                trace.row_parent = *state;
            }
        }
        peak_states = peak_states.max(states.len());
        if progress {
            eprintln!(
                "grammar_query step={completed}/{} row={} col={} states={} generated={} total_transitions={} step_seconds={:.3} elapsed_seconds={:.3} rss_kib={} peak_rss_kib={}",
                schedule.len(),
                step.row,
                step.col,
                states.len(),
                generated,
                generated_transitions,
                step_started.elapsed().as_secs_f64(),
                started.elapsed().as_secs_f64(),
                process_memory_kib("VmRSS:").map_or("unknown".into(), |value| value.to_string()),
                process_memory_kib("VmHWM:").map_or("unknown".into(), |value| value.to_string()),
            );
        }
    }
    let minimum_good_u = states
        .iter()
        .filter_map(|(state, trace)| (!state.violated).then_some(trace.cost))
        .min();
    let minimum_bad_u = states
        .iter()
        .filter_map(|(state, trace)| state.violated.then_some(trace.cost))
        .min();
    let bad_witness_rows = match (row_parents, minimum_bad_u) {
        (Some(parents), Some(cost)) => {
            let terminal = states
                .iter()
                .filter(|(state, trace)| state.violated && trace.cost == cost)
                .map(|(state, _)| *state)
                .min_by_key(|state| (state.frontier.0, state.violated))
                .expect("minimum bad cost must have a terminal state");
            Some(backtrack_grammar_witness(n, &parents, terminal)?)
        }
        _ => None,
    };
    Ok(GrammarQueryStats {
        minimum_good_u,
        minimum_bad_u,
        peak_states,
        generated_transitions,
        elapsed: started.elapsed(),
        bad_witness_rows,
    })
}

fn backtrack_grammar_witness(
    n: usize,
    row_parents: &[FastMap<GrammarHistoryState, (GrammarHistoryState, u32)>],
    mut target: GrammarHistoryState,
) -> Result<Vec<u32>, String> {
    if row_parents.len() != n {
        return Err("grammar witness recovery requires every row-boundary layer".into());
    }
    let mut rows = Vec::with_capacity(n);
    for row in (0..n).rev() {
        let (parent, row_mask) = row_parents[row]
            .get(&target)
            .copied()
            .ok_or_else(|| format!("no grammar witness predecessor at row {row}"))?;
        target = parent;
        rows.push(row_mask);
    }
    if target.frontier != State::new(0, 0) || target.violated {
        return Err("grammar witness did not backtrack to the initial state".into());
    }
    rows.reverse();
    Ok(rows)
}

fn write_grammar_witness(path: &Path, n: usize, rows: &[u32]) -> Result<(), String> {
    if rows.len() != n {
        return Err("grammar witness has the wrong row count".into());
    }
    let rendered = rows
        .iter()
        .map(|mask| {
            (0..n)
                .map(|col| if mask & (1 << col) != 0 { 'U' } else { '.' })
                .collect::<String>()
        })
        .collect::<Vec<_>>()
        .join("\n")
        + "\n";
    fs::write(path, rendered).map_err(|error| {
        format!(
            "failed to write grammar witness {}: {error}",
            path.display()
        )
    })
}

fn centered_violation_flags(
    side: usize,
    square_bits: u128,
    thresholds: CenteredThresholds,
) -> Result<u8, String> {
    let row_mask = (1u128 << side) - 1;
    let rows = (0..side).map(|row| (square_bits >> (row * side)) & row_mask);
    let summary = CenteredSquareMonitor::from_row_masks(side, rows)?
        .profile(side)?
        .port_word;
    Ok(
        u8::from(summary.repeated_components > thresholds.repeated_components)
            | (u8::from(
                summary.maximum_cyclic_runs_per_component > thresholds.maximum_cyclic_runs,
            ) << 1)
            | (u8::from(summary.compressed_linear_run_count > thresholds.compressed_runs) << 2),
    )
}

fn centered_summary_violation_flags(
    summary: &grid_graphs::exact_centered_square::PortWordSummary,
    thresholds: CenteredThresholds,
) -> u8 {
    u8::from(summary.repeated_components > thresholds.repeated_components)
        | (u8::from(summary.maximum_cyclic_runs_per_component > thresholds.maximum_cyclic_runs)
            << 1)
        | (u8::from(summary.compressed_linear_run_count > thresholds.compressed_runs) << 2)
}

fn backtrack_centered_witness(
    n: usize,
    row_parents: &[FastMap<CenteredProductState, (CenteredProductState, u32)>],
    mut target: CenteredProductState,
    initial: CenteredProductState,
) -> Result<Vec<u32>, String> {
    if row_parents.len() != n {
        return Err("centered witness recovery requires every row-boundary layer".into());
    }
    let mut rows = Vec::with_capacity(n);
    for row in (0..n).rev() {
        let (parent, row_mask) = row_parents[row]
            .get(&target)
            .copied()
            .ok_or_else(|| format!("no centered witness predecessor at row {row}"))?;
        rows.push(row_mask);
        target = parent;
    }
    if target != initial {
        return Err("centered witness did not backtrack to the initial state".into());
    }
    rows.reverse();
    Ok(rows)
}

fn centered_product_search(
    n: usize,
    target: usize,
    side: usize,
    thresholds: CenteredThresholds,
    progress: bool,
    recover_witness: bool,
) -> Result<CenteredProductStats, String> {
    if n == 0 || n > MAX_N {
        return Err(format!("n must be in 1..={MAX_N}"));
    }
    if target > n * n {
        return Err(format!("U count cannot exceed {}", n * n));
    }
    if side < 2 || side > n || side % 2 != n % 2 {
        return Err(format!(
            "--side must be in 2..={n} and have the same parity as n"
        ));
    }
    let started = Instant::now();
    let schedule = steps(n)?;
    let threshold_automaton = ThresholdAutomaton::build(side, thresholds, progress)?;
    if progress {
        eprintln!(
            "threshold_automaton exact_peak={} quotient_peak={} terminal_classes={}",
            threshold_automaton
                .exact_layer_counts
                .iter()
                .copied()
                .max()
                .unwrap_or(0),
            threshold_automaton
                .quotient_layer_counts
                .iter()
                .copied()
                .max()
                .unwrap_or(0),
            threshold_automaton.outputs.len()
        );
    }
    let dual_nodes = (n - 1) * (n - 1) + 1;
    let offset = (n - side) / 2;
    let closing_step = (offset + side - 1) * n + offset + side - 1;
    let initial = CenteredProductState {
        frontier: State::new(0, 0),
        u_count: 0,
        centered: CenteredProduct::Streaming(threshold_automaton.initial),
    };
    let mut states: FastMap<CenteredProductState, CenteredProductTrace> =
        FastMap::with_hasher(BuildHasherDefault::default());
    states.insert(initial, CenteredProductTrace { row_parent: 0 });
    let mut row_start_states = vec![initial];
    let mut row_parents: Option<Vec<FastMap<CenteredProductState, (CenteredProductState, u32)>>> =
        recover_witness.then(Vec::new);
    let mut peak_states = 1;
    let mut generated_transitions = 0u64;
    let mut equivalent_merges = 0u64;
    let mut state_counts = vec![1];

    for (index, step) in schedule.iter().enumerate() {
        let step_started = Instant::now();
        let remaining = schedule.len() - index - 1;
        let mut transition_cache: FastMap<(State, bool), Option<State>> =
            FastMap::with_hasher(BuildHasherDefault::default());
        let expected_next = if index == closing_step {
            states.len().div_ceil(64).max(1024)
        } else {
            states.len().saturating_mul(5).div_ceil(4)
        };
        let mut next: FastMap<CenteredProductState, CenteredProductTrace> =
            FastMap::with_capacity_and_hasher(expected_next, BuildHasherDefault::default());
        let is_local = (offset..offset + side).contains(&step.row)
            && (offset..offset + side).contains(&step.col);
        let local_position = is_local.then(|| (step.row - offset) * side + step.col - offset);
        for (history, trace) in states {
            for chosen in [false, true] {
                let next_count = history.u_count + u16::from(chosen);
                if next_count as usize > target || next_count as usize + remaining < target {
                    continue;
                }
                generated_transitions += 1;
                let frontier = *transition_cache
                    .entry((history.frontier, chosen))
                    .or_insert_with(|| advance(history.frontier, step, chosen));
                let Some(frontier) = frontier else {
                    continue;
                };
                let components = component_count(frontier.labels(), step.after_indices.len());
                let current_rank = step.introduced_nodes - components;
                let rank_deficit = (dual_nodes - 1) - current_rank;
                if next_count as usize + rank_deficit.div_ceil(2) > target {
                    continue;
                }
                let centered = match history.centered {
                    CenteredProduct::Profile(flags) => CenteredProduct::Profile(flags),
                    CenteredProduct::Streaming(local_id) => {
                        let next_id = if let Some(local_position) = local_position {
                            threshold_automaton.transitions[local_position][local_id as usize]
                                [usize::from(chosen)]
                        } else {
                            local_id
                        };
                        if index == closing_step {
                            CenteredProduct::Profile(threshold_automaton.outputs[next_id as usize])
                        } else {
                            CenteredProduct::Streaming(next_id)
                        }
                    }
                };
                let candidate = CenteredProductState {
                    frontier,
                    u_count: next_count,
                    centered,
                };
                if next
                    .insert(
                        candidate,
                        CenteredProductTrace {
                            row_parent: trace.row_parent,
                        },
                    )
                    .is_some()
                {
                    equivalent_merges += 1;
                }
            }
        }
        states = next;
        let completed = index + 1;
        if completed % n == 0 {
            if let Some(layers) = &mut row_parents {
                layers.push(
                    states
                        .iter()
                        .map(|(&state, trace)| {
                            (
                                state,
                                (
                                    row_start_states[trace.row_parent as usize],
                                    state.frontier.row_u(),
                                ),
                            )
                        })
                        .collect(),
                );
            }
            row_start_states = Vec::with_capacity(states.len());
            for (index, (state, trace)) in states.iter_mut().enumerate() {
                row_start_states.push(*state);
                trace.row_parent = index as u32;
            }
        }
        peak_states = peak_states.max(states.len());
        state_counts.push(states.len());
        if progress {
            eprintln!(
                "centered_product step={completed}/{} row={} col={} phase={} states={} capacity={} local_states={} frontier_transition_classes={} key_bytes={} trace_bytes={} generated={} merges={} step_seconds={:.3} elapsed_seconds={:.3} rss_kib={} peak_rss_kib={}",
                schedule.len(), step.row, step.col,
                if index < closing_step { "prefix" } else { "profile" },
                states.len(), states.capacity(),
                local_position.map_or(0, |position| threshold_automaton.quotient_layer_counts[position + 1]),
                transition_cache.len(),
                std::mem::size_of::<CenteredProductState>(),
                std::mem::size_of::<CenteredProductTrace>(),
                generated_transitions, equivalent_merges,
                step_started.elapsed().as_secs_f64(), started.elapsed().as_secs_f64(),
                process_memory_kib("VmRSS:").map_or("unknown".into(), |value| value.to_string()),
                process_memory_kib("VmHWM:").map_or("unknown".into(), |value| value.to_string()),
            );
        }
    }

    let connected = !states.is_empty();
    let violation_flags = states
        .keys()
        .filter_map(|state| match state.centered {
            CenteredProduct::Profile(flags) => Some(flags),
            CenteredProduct::Streaming(_) => None,
        })
        .fold(0, |all, flags| all | flags);
    let witness_rows = if violation_flags == 0 {
        None
    } else if let Some(parents) = row_parents {
        let terminal = states
            .keys()
            .filter(|state| matches!(state.centered, CenteredProduct::Profile(flags) if flags != 0))
            .min_by_key(|state| {
                let CenteredProduct::Profile(flags) = state.centered else {
                    unreachable!()
                };
                (state.frontier.0, flags)
            })
            .copied()
            .expect("nonzero violation flags require a terminal state");
        Some(backtrack_centered_witness(n, &parents, terminal, initial)?)
    } else {
        None
    };
    Ok(CenteredProductStats {
        connected,
        violation_flags,
        peak_states,
        generated_transitions,
        equivalent_merges,
        state_counts,
        elapsed: started.elapsed(),
        witness_rows,
    })
}

fn write_centered_witness(path: &Path, n: usize, rows: &[u32]) -> Result<(), String> {
    write_grammar_witness(path, n, rows)
}

fn verify_centered_witness(
    n: usize,
    target: usize,
    side: usize,
    thresholds: CenteredThresholds,
    rows: &[u32],
) -> Result<(), String> {
    if rows.len() != n
        || rows
            .iter()
            .map(|row| row.count_ones() as usize)
            .sum::<usize>()
            != target
    {
        return Err("recovered centered witness has the wrong dimensions or U count".into());
    }
    let mut frontier = State::new(0, 0);
    for step in steps(n)? {
        let chosen = rows[step.row] & (1 << step.col) != 0;
        frontier = advance(frontier, &step, chosen)
            .ok_or("recovered centered witness fails global connectivity")?;
    }
    let offset = (n - side) / 2;
    let mut square_bits = 0u128;
    for row in 0..side {
        for col in 0..side {
            if rows[offset + row] & (1 << (offset + col)) != 0 {
                square_bits |= 1 << (row * side + col);
            }
        }
    }
    if centered_violation_flags(side, square_bits, thresholds)? == 0 {
        return Err("recovered centered witness does not violate a threshold".into());
    }
    Ok(())
}

fn apply_row_pruning(
    mut states: FastMap<State, u16>,
    mode: PruningMode,
    n: usize,
    target: usize,
    schedule: &[Step],
    completed: usize,
) -> (FastMap<State, u16>, u64, u64, u64) {
    let step = &schedule[completed - 1];
    debug_assert_eq!(completed % n, 0);
    let mut mirror_merges = 0;
    let mut geometry_prunes = 0;
    let mut closure_prunes = 0;

    if mode.mirror() {
        let before = states.len();
        let mut canonical: FastMap<State, u16> = FastMap::with_capacity_and_hasher(
            states.len().div_ceil(2),
            BuildHasherDefault::default(),
        );
        for (state, cost) in states {
            let reflected = reflected_row_boundary_state(state, step, n);
            let representative = State(state.0.min(reflected.0));
            canonical
                .entry(representative)
                .and_modify(|existing| *existing = (*existing).min(cost))
                .or_insert(cost);
        }
        mirror_merges = (before - canonical.len()) as u64;
        states = canonical;
    }

    if mode.geometry() {
        let dual_nodes = (n - 1) * (n - 1) + 1;
        let future_cells = n * n - completed;
        let before = states.len();
        states.retain(|state, cost| {
            let components = component_count(state.labels(), step.after_indices.len());
            let current_rank = step.introduced_nodes - components;
            let rank_deficit = (dual_nodes - 1) - current_rank;
            let future_u = (target - *cost as usize).min(future_cells);
            let maximum_future_edges = if future_u == 0 {
                0
            } else {
                2 * future_u - future_u.div_ceil(n)
            };
            maximum_future_edges >= rank_deficit
        });
        geometry_prunes = (before - states.len()) as u64;
    }

    if mode.closure() {
        let mut profiles: FastMap<u32, ClosureProfile> =
            FastMap::with_hasher(BuildHasherDefault::default());
        let before = states.len();
        states.retain(|state, _| {
            let profile = profiles
                .entry(state.row_u())
                .or_insert_with(|| closure_profile(n, schedule, completed, step, state.row_u()));
            closure_can_connect(*state, step.after_indices.len(), profile)
        });
        closure_prunes = (before - states.len()) as u64;
    }

    (states, mirror_merges, geometry_prunes, closure_prunes)
}

fn transition_diagnostic(
    state: State,
    cost: u16,
    step: &Step,
    chosen: bool,
    target: usize,
    dual_nodes: usize,
) -> String {
    let next_cost = cost + u16::from(chosen);
    if next_cost as usize > target {
        return format!("{{\"chosen\":{chosen},\"outcome\":\"budget\"}}");
    }
    let Some(next) = advance(state, step, chosen) else {
        return format!("{{\"chosen\":{chosen},\"outcome\":\"retired_component\"}}");
    };
    let components = component_count(next.labels(), step.after_indices.len());
    let current_rank = step.introduced_nodes - components;
    let rank_deficit = (dual_nodes - 1) - current_rank;
    let minimum_additional_u = rank_deficit.div_ceil(2);
    if next_cost as usize + minimum_additional_u > target {
        return format!(
            "{{\"chosen\":{chosen},\"outcome\":\"rank\",\"next_cost\":{next_cost},\"components\":{components},\"rank_deficit\":{rank_deficit}}}"
        );
    }
    format!(
        "{{\"chosen\":{chosen},\"outcome\":\"accepted\",\"next_cost\":{next_cost},\"next_state\":\"0x{:x}\",\"components\":{components},\"rank_deficit\":{rank_deficit}}}",
        next.0
    )
}

fn dump_states(
    path: &Path,
    n: usize,
    target: usize,
    completed: usize,
    schedule: &[Step],
    states: &FastMap<State, u16>,
) -> Result<(), String> {
    if completed == 0 || completed > schedule.len() {
        return Err(format!("cannot dump completed step {completed}"));
    }
    let step = &schedule[completed - 1];
    let after_nodes: Vec<_> = step
        .after_indices
        .iter()
        .map(|&index| step.nodes[index])
        .collect();
    let mut entries: Vec<_> = states.iter().map(|(&state, &cost)| (state, cost)).collect();
    entries.sort_unstable_by_key(|(state, cost)| (state.0, *cost));
    let dual_nodes = (n - 1) * (n - 1) + 1;
    let out = dual_nodes - 1;
    let mut output = String::new();
    writeln!(output, "{{").unwrap();
    writeln!(
        output,
        "  \"schema\": \"grid-graphs.frontier-state-dump.v1\","
    )
    .unwrap();
    writeln!(output, "  \"n\": {n},").unwrap();
    writeln!(output, "  \"target\": {target},").unwrap();
    writeln!(output, "  \"completed_steps\": {completed},").unwrap();
    writeln!(
        output,
        "  \"processed_cell\": [{}, {}],",
        step.row, step.col
    )
    .unwrap();
    writeln!(output, "  \"row_mask_current_columns\": [0, {}],", step.col).unwrap();
    if step.col + 1 < n {
        writeln!(
            output,
            "  \"row_mask_previous_columns\": [{}, {}],",
            step.col + 1,
            n - 1
        )
        .unwrap();
    } else {
        writeln!(output, "  \"row_mask_previous_columns\": null,").unwrap();
    }
    write!(output, "  \"after_nodes\": [").unwrap();
    for (slot, &node) in after_nodes.iter().enumerate() {
        if slot > 0 {
            output.push_str(", ");
        }
        if node == out {
            write!(
                output,
                "{{\"slot\":{slot},\"node\":{node},\"kind\":\"OUT\"}}"
            )
            .unwrap();
        } else {
            write!(
                output,
                "{{\"slot\":{slot},\"node\":{node},\"kind\":\"face\",\"face\":[{},{}]}}",
                node / (n - 1),
                node % (n - 1)
            )
            .unwrap();
        }
    }
    output.push_str("],\n");
    writeln!(output, "  \"state_count\": {},", entries.len()).unwrap();
    writeln!(output, "  \"states\": [").unwrap();
    for (entry_index, (state, cost)) in entries.iter().enumerate() {
        let labels: Vec<_> = (0..after_nodes.len())
            .map(|slot| label_at(state.labels(), slot))
            .collect();
        let row_bits: String = (0..n)
            .map(|col| {
                if state.row_u() & (1 << col) != 0 {
                    'U'
                } else {
                    '.'
                }
            })
            .collect();
        let transitions = if completed < schedule.len() {
            let next_step = &schedule[completed];
            format!(
                "[{},{}]",
                transition_diagnostic(*state, *cost, next_step, false, target, dual_nodes),
                transition_diagnostic(*state, *cost, next_step, true, target, dual_nodes)
            )
        } else {
            "[]".into()
        };
        write!(
            output,
            "    {{\"packed_state\":\"0x{:x}\",\"cost\":{},\"row_u\":{},\"row_bits_col0_first\":\"{}\",\"labels\":[{}],\"next_transitions\":{}}}",
            state.0,
            cost,
            state.row_u(),
            row_bits,
            labels
                .iter()
                .map(|label| label.to_string())
                .collect::<Vec<_>>()
                .join(","),
            transitions
        )
        .unwrap();
        if entry_index + 1 < entries.len() {
            output.push(',');
        }
        output.push('\n');
    }
    output.push_str("  ]\n}\n");
    fs::write(path, output)
        .map_err(|error| format!("failed to write state dump {}: {error}", path.display()))
}

fn parse_pattern(path: &Path, n: usize) -> Result<Vec<Vec<bool>>, String> {
    let contents = fs::read_to_string(path)
        .map_err(|error| format!("failed to read pattern {}: {error}", path.display()))?;
    let mut rows = Vec::new();
    for line in contents.lines() {
        let line = line.trim();
        if line.is_empty()
            || line.starts_with('#')
            || !line.bytes().all(|ch| ch == b'U' || ch == b'.')
        {
            continue;
        }
        if line.len() != n {
            return Err(format!(
                "pattern row has width {}, expected {n}",
                line.len()
            ));
        }
        rows.push(line.bytes().map(|ch| ch == b'U').collect());
    }
    if rows.len() != n {
        return Err(format!("pattern has {} rows, expected {n}", rows.len()));
    }
    Ok(rows)
}

fn replay_pattern(
    pattern_path: &Path,
    output_path: &Path,
    n: usize,
    mode: PruningMode,
) -> Result<(), String> {
    if mode != PruningMode::None && mode != PruningMode::Mirror {
        return Err("pattern replay supports only none or mirror pruning".into());
    }
    let pattern = parse_pattern(pattern_path, n)?;
    let schedule = steps(n)?;
    let mut state = State::new(0, 0);
    let mut cost = 0u16;
    let mut reflected_orientation = false;
    let mut records = Vec::new();
    for (index, step) in schedule.iter().enumerate() {
        let source_col = if reflected_orientation {
            n - 1 - step.col
        } else {
            step.col
        };
        let chosen = pattern[step.row][source_col];
        state = advance(state, step, chosen).ok_or_else(|| {
            format!(
                "pattern seals a dual component at step {} ({},{})",
                index + 1,
                step.row,
                step.col
            )
        })?;
        cost += u16::from(chosen);
        let mut reflected_at_boundary = false;
        if mode.mirror() && (index + 1) % n == 0 {
            let reflected = reflected_row_boundary_state(state, step, n);
            if reflected.0 < state.0 {
                state = reflected;
                reflected_orientation = !reflected_orientation;
                reflected_at_boundary = true;
            }
        }
        if (index + 1) % n == 0 || index + 4 >= schedule.len() {
            let after_nodes: Vec<_> = step
                .after_indices
                .iter()
                .map(|&slot| step.nodes[slot])
                .collect();
            let labels: Vec<_> = (0..after_nodes.len())
                .map(|slot| label_at(state.labels(), slot))
                .collect();
            records.push(format!(
                "{{\"completed_steps\":{},\"processed_cell\":[{},{}],\"source_col\":{},\"chosen\":{},\"cost\":{},\"packed_state\":\"0x{:x}\",\"row_u\":{},\"labels\":[{}],\"after_nodes\":[{}],\"orientation_reflected\":{},\"reflected_at_boundary\":{}}}",
                index + 1,
                step.row,
                step.col,
                source_col,
                chosen,
                cost,
                state.0,
                state.row_u(),
                labels.iter().map(|value| value.to_string()).collect::<Vec<_>>().join(","),
                after_nodes.iter().map(|value| value.to_string()).collect::<Vec<_>>().join(","),
                reflected_orientation,
                reflected_at_boundary,
            ));
        }
    }
    let output = format!(
        "{{\n  \"schema\": \"grid-graphs.frontier-pattern-replay.v1\",\n  \"n\": {n},\n  \"pattern\": \"{}\",\n  \"pruning\": \"{mode:?}\",\n  \"u_count\": {cost},\n  \"accepted\": true,\n  \"records\": [\n    {}\n  ]\n}}\n",
        pattern_path.display(),
        records.join(",\n    ")
    );
    fs::write(output_path, output)
        .map_err(|error| format!("failed to write replay {}: {error}", output_path.display()))
}

fn process_memory_kib(field: &str) -> Option<u64> {
    let status = fs::read_to_string("/proc/self/status").ok()?;
    status.lines().find_map(|line| {
        let value = line.strip_prefix(field)?.trim();
        value.split_whitespace().next()?.parse().ok()
    })
}

fn checkpoint_checksum(mut checksum: u64, bytes: &[u8]) -> u64 {
    for &byte in bytes {
        checksum ^= u64::from(byte);
        checksum = checksum.wrapping_mul(0x100000001b3);
    }
    checksum
}

fn write_checkpoint(
    path: &Path,
    n: usize,
    target: usize,
    completed_steps: usize,
    peak_states: usize,
    generated_transitions: u64,
    states: &FastMap<State, u16>,
) -> Result<(), String> {
    if let Some(parent) = path
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
    {
        fs::create_dir_all(parent)
            .map_err(|error| format!("failed to create {}: {error}", parent.display()))?;
    }
    let mut temporary_name = path.as_os_str().to_owned();
    temporary_name.push(format!(".tmp.{}", process::id()));
    let temporary = PathBuf::from(temporary_name);
    let file = fs::File::create(&temporary)
        .map_err(|error| format!("failed to create {}: {error}", temporary.display()))?;
    let mut writer = BufWriter::new(file);
    let mut header = [0u8; CHECKPOINT_HEADER_BYTES as usize];
    header[..8].copy_from_slice(CHECKPOINT_MAGIC);
    header[8..12].copy_from_slice(&(n as u32).to_le_bytes());
    header[12..16].copy_from_slice(&(target as u32).to_le_bytes());
    header[16..20].copy_from_slice(&(completed_steps as u32).to_le_bytes());
    header[20..28].copy_from_slice(&(peak_states as u64).to_le_bytes());
    header[28..36].copy_from_slice(&generated_transitions.to_le_bytes());
    header[36..44].copy_from_slice(&(states.len() as u64).to_le_bytes());
    writer
        .write_all(&header)
        .map_err(|error| format!("failed to write {}: {error}", temporary.display()))?;
    let mut checksum = checkpoint_checksum(0xcbf29ce484222325, &header);
    for (&state, &cost) in states {
        let mut record = [0u8; 18];
        record[..16].copy_from_slice(&state.0.to_le_bytes());
        record[16..].copy_from_slice(&cost.to_le_bytes());
        checksum = checkpoint_checksum(checksum, &record);
        writer
            .write_all(&record)
            .map_err(|error| format!("failed to write {}: {error}", temporary.display()))?;
    }
    writer
        .write_all(&checksum.to_le_bytes())
        .map_err(|error| format!("failed to write {}: {error}", temporary.display()))?;
    writer
        .flush()
        .map_err(|error| format!("failed to flush {}: {error}", temporary.display()))?;
    let file = writer
        .into_inner()
        .map_err(|error| format!("failed to finish {}: {error}", temporary.display()))?;
    file.sync_all()
        .map_err(|error| format!("failed to sync {}: {error}", temporary.display()))?;
    fs::rename(&temporary, path).map_err(|error| {
        format!(
            "failed to replace checkpoint {} with {}: {error}",
            path.display(),
            temporary.display()
        )
    })?;
    if let Some(parent) = path
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
    {
        fs::File::open(parent)
            .and_then(|directory| directory.sync_all())
            .map_err(|error| format!("failed to sync {}: {error}", parent.display()))?;
    }
    Ok(())
}

fn read_checkpoint(path: &Path, n: usize, target: usize) -> Result<Checkpoint, String> {
    let file = fs::File::open(path)
        .map_err(|error| format!("failed to open checkpoint {}: {error}", path.display()))?;
    let file_bytes = file
        .metadata()
        .map_err(|error| format!("failed to inspect checkpoint {}: {error}", path.display()))?
        .len();
    let mut reader = BufReader::new(file);
    let mut header = [0u8; CHECKPOINT_HEADER_BYTES as usize];
    reader
        .read_exact(&mut header)
        .map_err(|error| format!("failed to read checkpoint {}: {error}", path.display()))?;
    if &header[..8] != CHECKPOINT_MAGIC {
        return Err(format!("checkpoint {} has invalid magic", path.display()));
    }
    let read_u32 =
        |offset: usize| u32::from_le_bytes(header[offset..offset + 4].try_into().unwrap()) as usize;
    let read_u64 =
        |offset: usize| u64::from_le_bytes(header[offset..offset + 8].try_into().unwrap());
    let stored_n = read_u32(8);
    let stored_target = read_u32(12);
    let completed_steps = read_u32(16);
    let peak_states = read_u64(20) as usize;
    let generated_transitions = read_u64(28);
    let count = read_u64(36) as usize;
    if stored_n != n || stored_target != target {
        return Err(format!(
            "checkpoint parameters are n={stored_n}, target={stored_target}; requested n={n}, target={target}"
        ));
    }
    if completed_steps > n * n || completed_steps % n != 0 {
        return Err(format!(
            "checkpoint has invalid completed step count {completed_steps}"
        ));
    }
    let expected_bytes = CHECKPOINT_RECORD_BYTES
        .checked_mul(count as u64)
        .and_then(|bytes| bytes.checked_add(CHECKPOINT_HEADER_BYTES + CHECKPOINT_TRAILER_BYTES))
        .ok_or_else(|| format!("checkpoint {} has an invalid state count", path.display()))?;
    if file_bytes != expected_bytes {
        return Err(format!(
            "checkpoint {} has {file_bytes} bytes, expected {expected_bytes}",
            path.display()
        ));
    }
    let bag_slots = if completed_steps == 0 {
        1
    } else {
        steps(n)?[completed_steps - 1].after_indices.len()
    };
    let mut states = FastMap::with_capacity_and_hasher(count, BuildHasherDefault::default());
    let mut record = [0u8; 18];
    let mut checksum = checkpoint_checksum(0xcbf29ce484222325, &header);
    for _ in 0..count {
        reader
            .read_exact(&mut record)
            .map_err(|error| format!("failed to read checkpoint {}: {error}", path.display()))?;
        checksum = checkpoint_checksum(checksum, &record);
        let state = State(u128::from_le_bytes(record[..16].try_into().unwrap()));
        let cost = u16::from_le_bytes(record[16..].try_into().unwrap());
        let valid_bits = LABEL_MASK | (ROW_MASK << ROW_SHIFT);
        let labels = state.labels();
        let mut maximum_label = 0;
        let canonical = (0..bag_slots).all(|slot| {
            let label = label_at(labels, slot);
            let valid = (slot == 0 && label == 0) || (slot > 0 && label <= maximum_label + 1);
            maximum_label = maximum_label.max(label);
            valid
        });
        let labels_fit = labels >> (LABEL_BITS * bag_slots) == 0;
        let row_fits = state.row_u() < 1 << n;
        if state.0 & !valid_bits != 0
            || !canonical
            || !labels_fit
            || !row_fits
            || cost as usize > target
            || state.row_u().count_ones() > u32::from(cost)
        {
            return Err(format!(
                "checkpoint {} contains an invalid state record",
                path.display()
            ));
        }
        if states.insert(state, cost).is_some() {
            return Err(format!(
                "checkpoint {} contains a duplicate state",
                path.display()
            ));
        }
    }
    let mut stored_checksum = [0u8; 8];
    reader
        .read_exact(&mut stored_checksum)
        .map_err(|error| format!("failed to finish checkpoint {}: {error}", path.display()))?;
    if u64::from_le_bytes(stored_checksum) != checksum {
        return Err(format!("checkpoint {} has a bad checksum", path.display()));
    }
    Ok(Checkpoint {
        completed_steps,
        peak_states,
        generated_transitions,
        states,
    })
}

#[cfg(test)]
fn search(n: usize, target: usize) -> Result<SearchStats, String> {
    search_with_options(n, target, SearchOptions::default())
}

fn search_with_options(
    n: usize,
    target: usize,
    options: SearchOptions<'_>,
) -> Result<SearchStats, String> {
    if n == 0 || n > MAX_N {
        return Err(format!("n must be in 1..={MAX_N}"));
    }
    if target > n * n {
        return Err(format!("U count cannot exceed {}", n * n));
    }
    if options.resume && options.checkpoint.is_none() {
        return Err("--resume requires --checkpoint".into());
    }
    let started = Instant::now();
    let schedule = steps(n)?;
    let dual_nodes = (n - 1) * (n - 1) + 1;
    let (completed_steps, mut states, mut peak_states, mut generated_transitions) =
        if options.resume {
            let checkpoint = read_checkpoint(options.checkpoint.unwrap(), n, target)?;
            (
                checkpoint.completed_steps,
                checkpoint.states,
                checkpoint.peak_states,
                checkpoint.generated_transitions,
            )
        } else {
            let mut states = FastMap::with_hasher(BuildHasherDefault::default());
            states.insert(State::new(0, 0), 0u16);
            (0, states, 1, 0)
        };
    let mut mirror_merges = 0u64;
    let mut geometry_prunes = 0u64;
    let mut closure_prunes = 0u64;
    if completed_steps > 0 && options.pruning != PruningMode::None {
        let (pruned, mirror, geometry, closure) = apply_row_pruning(
            states,
            options.pruning,
            n,
            target,
            &schedule,
            completed_steps,
        );
        states = pruned;
        mirror_merges += mirror;
        geometry_prunes += geometry;
        closure_prunes += closure;
    }
    let mut state_counts = vec![0; completed_steps];
    state_counts.push(states.len());
    if options.dump_step == Some(completed_steps) {
        dump_states(
            options.dump_out.unwrap(),
            n,
            target,
            completed_steps,
            &schedule,
            &states,
        )?;
    }
    if options.progress && completed_steps > 0 {
        eprintln!(
            "resumed step={completed_steps}/{} states={} peak_states={} transitions={} rss_kib={}",
            schedule.len(),
            states.len(),
            peak_states,
            generated_transitions,
            process_memory_kib("VmRSS:").map_or("unknown".into(), |value| value.to_string())
        );
    }
    for (index, step) in schedule.iter().enumerate().skip(completed_steps) {
        let step_started = Instant::now();
        let entries: Vec<(State, u16)> = states.into_iter().collect();
        let (next, generated) = extend_chunk(&entries, step, target, dual_nodes);
        generated_transitions += generated;
        states = next;
        let completed = index + 1;
        let (step_mirror, step_geometry, step_closure) = if completed % n == 0 {
            let (pruned, mirror, geometry, closure) =
                apply_row_pruning(states, options.pruning, n, target, &schedule, completed);
            states = pruned;
            (mirror, geometry, closure)
        } else {
            (0, 0, 0)
        };
        mirror_merges += step_mirror;
        geometry_prunes += step_geometry;
        closure_prunes += step_closure;
        peak_states = peak_states.max(states.len());
        state_counts.push(states.len());
        if options.dump_step == Some(completed) {
            dump_states(
                options.dump_out.unwrap(),
                n,
                target,
                completed,
                &schedule,
                &states,
            )?;
        }
        if options.progress {
            eprintln!(
                "step={completed}/{} row={} col={} states={} generated={} mirror_merged={} geometry_pruned={} closure_pruned={} total_transitions={} step_seconds={:.3} elapsed_seconds={:.3} rss_kib={} peak_rss_kib={}",
                schedule.len(),
                step.row,
                step.col,
                states.len(),
                generated,
                step_mirror,
                step_geometry,
                step_closure,
                generated_transitions,
                step_started.elapsed().as_secs_f64(),
                started.elapsed().as_secs_f64(),
                process_memory_kib("VmRSS:").map_or("unknown".into(), |value| value.to_string()),
                process_memory_kib("VmHWM:").map_or("unknown".into(), |value| value.to_string()),
            );
        }
        if completed % n == 0 {
            if let Some(path) = options.checkpoint {
                let checkpoint_started = Instant::now();
                write_checkpoint(
                    path,
                    n,
                    target,
                    completed,
                    peak_states,
                    generated_transitions,
                    &states,
                )?;
                if options.progress {
                    eprintln!(
                        "checkpoint={} step={completed} states={} seconds={:.3}",
                        path.display(),
                        states.len(),
                        checkpoint_started.elapsed().as_secs_f64()
                    );
                }
            }
        }
    }

    let minimum_u = states.values().copied().min();
    Ok(SearchStats {
        feasible: minimum_u.is_some_and(|cost| cost as usize <= target),
        minimum_u,
        peak_states,
        generated_transitions,
        state_counts,
        state_count_start: completed_steps,
        elapsed: started.elapsed(),
        peak_rss_kib: process_memory_kib("VmHWM:"),
        mirror_merges,
        geometry_prunes,
        closure_prunes,
    })
}

struct Config {
    n: usize,
    target: usize,
    meeting_step: Option<usize>,
    per_step: bool,
    progress: bool,
    checkpoint: Option<PathBuf>,
    resume: bool,
    pruning: PruningMode,
    dump_step: Option<usize>,
    dump_out: Option<PathBuf>,
    replay_pattern: Option<PathBuf>,
    replay_out: Option<PathBuf>,
    grammar_violation_query: bool,
    grammar_violation_kind: GrammarViolationKind,
    grammar_witness_out: Option<PathBuf>,
}

fn parse_args() -> Result<Config, String> {
    let args: Vec<String> = env::args().skip(1).collect();
    let mut n = None;
    let mut target = None;
    let mut meeting_step = None;
    let mut per_step = false;
    let mut progress = false;
    let mut checkpoint = None;
    let mut resume = false;
    let mut pruning = PruningMode::None;
    let mut dump_step = None;
    let mut dump_out = None;
    let mut replay_pattern = None;
    let mut replay_out = None;
    let mut grammar_violation_query = false;
    let mut grammar_violation_kind = GrammarViolationKind::Combined;
    let mut grammar_witness_out = None;
    let mut at = 0;
    while at < args.len() {
        match args[at].as_str() {
            "--per-step" => {
                per_step = true;
                at += 1;
            }
            "--progress" => {
                progress = true;
                at += 1;
            }
            "--grammar-violation-query" => {
                grammar_violation_query = true;
                at += 1;
            }
            "--resume" => {
                resume = true;
                at += 1;
            }
            "--n"
            | "--u-count"
            | "--meet-step"
            | "--checkpoint"
            | "--pruning"
            | "--dump-step"
            | "--dump-out"
            | "--replay-pattern"
            | "--replay-out"
            | "--grammar-witness-out"
            | "--grammar-violation-kind" => {
                let flag = args[at].clone();
                let value = args
                    .get(at + 1)
                    .ok_or_else(|| format!("missing value for {flag}"))?;
                if flag == "--n" {
                    n = Some(
                        value
                            .parse::<usize>()
                            .map_err(|_| format!("invalid integer for {flag}"))?,
                    );
                } else if flag == "--meet-step" {
                    meeting_step = Some(
                        value
                            .parse::<usize>()
                            .map_err(|_| format!("invalid integer for {flag}"))?,
                    );
                } else if flag == "--checkpoint" {
                    checkpoint = Some(PathBuf::from(value));
                } else if flag == "--pruning" {
                    pruning = PruningMode::parse(value)?;
                } else if flag == "--dump-step" {
                    dump_step = Some(
                        value
                            .parse::<usize>()
                            .map_err(|_| format!("invalid integer for {flag}"))?,
                    );
                } else if flag == "--dump-out" {
                    dump_out = Some(PathBuf::from(value));
                } else if flag == "--replay-pattern" {
                    replay_pattern = Some(PathBuf::from(value));
                } else if flag == "--replay-out" {
                    replay_out = Some(PathBuf::from(value));
                } else if flag == "--grammar-witness-out" {
                    grammar_witness_out = Some(PathBuf::from(value));
                } else if flag == "--grammar-violation-kind" {
                    grammar_violation_kind = GrammarViolationKind::parse(value)?;
                } else {
                    target = Some(
                        value
                            .parse::<usize>()
                            .map_err(|_| format!("invalid integer for {flag}"))?,
                    );
                }
                at += 2;
            }
            "--help" | "-h" => {
                println!(
                    "Usage: search_n17_frontier --n N --u-count K [options]\n\
                     Options:\n\
                       --meet-step T       diagnostic bidirectional search\n\
                       --per-step         print final per-step state counts\n\
                       --progress         print live timing and memory telemetry\n\
                       --pruning MODE     none|mirror|geometry|closure|all\n\
                       --checkpoint PATH  atomically checkpoint after every row\n\
                       --resume           resume the matching checkpoint\n\
                       --dump-step N      dump exact states after completed step N\n\
                       --dump-out PATH    state dump destination\n\
                       --replay-pattern P replay a U/. pattern through the frontier\n\
                        --replay-out PATH  replay report destination
                        --grammar-violation-query  split paths by any carrier/local-motif violation
                        --grammar-violation-kind K combined|support-hole|concurrent-carriers|local-motif|face-cut
                        --grammar-witness-out PATH recover one minimum violating U/. pattern"
                );
                process::exit(0);
            }
            option => return Err(format!("unknown option {option:?}")),
        }
    }
    if meeting_step.is_some() && (checkpoint.is_some() || resume || progress) {
        return Err("--meet-step cannot be combined with checkpoint, resume, or progress".into());
    }
    if resume && checkpoint.is_none() {
        return Err("--resume requires --checkpoint".into());
    }
    if dump_step.is_some() != dump_out.is_some() {
        return Err("--dump-step and --dump-out require each other".into());
    }
    if replay_pattern.is_some() != replay_out.is_some() {
        return Err("--replay-pattern and --replay-out require each other".into());
    }
    if grammar_violation_query
        && (meeting_step.is_some()
            || checkpoint.is_some()
            || resume
            || pruning != PruningMode::None
            || dump_step.is_some()
            || replay_pattern.is_some())
    {
        return Err("--grammar-violation-query supports only --progress and --per-step".into());
    }
    if grammar_witness_out.is_some() && !grammar_violation_query {
        return Err("--grammar-witness-out requires --grammar-violation-query".into());
    }
    Ok(Config {
        n: n.ok_or("--n is required")?,
        target: target.ok_or("--u-count is required")?,
        meeting_step,
        per_step,
        progress,
        checkpoint,
        resume,
        pruning,
        dump_step,
        dump_out,
        replay_pattern,
        replay_out,
        grammar_violation_query,
        grammar_violation_kind,
        grammar_witness_out,
    })
}

fn main() {
    let result = parse_args().and_then(|config| {
        if config.grammar_violation_query {
            let stats = grammar_violation_search(
                config.n,
                config.target,
                config.progress,
                config.grammar_witness_out.is_some(),
                config.grammar_violation_kind,
            )?;
            if let (Some(path), Some(rows)) =
                (&config.grammar_witness_out, &stats.bad_witness_rows)
            {
                write_grammar_witness(path, config.n, rows)?;
            }
            println!(
                "GRAMMAR_QUERY n={} u_count={} kind={:?} minimum_good_u={:?} minimum_bad_u={:?} peak_states={} transitions={} elapsed_seconds={:.3}",
                config.n,
                config.target,
                config.grammar_violation_kind,
                stats.minimum_good_u,
                stats.minimum_bad_u,
                stats.peak_states,
                stats.generated_transitions,
                stats.elapsed.as_secs_f64(),
            );
        } else if let Some(pattern) = &config.replay_pattern {
            replay_pattern(
                pattern,
                config.replay_out.as_ref().unwrap(),
                config.n,
                config.pruning,
            )?;
            println!(
                "replayed pattern={} n={} pruning={:?} output={}",
                pattern.display(),
                config.n,
                config.pruning,
                config.replay_out.as_ref().unwrap().display()
            );
        } else if let Some(meeting_step) = config.meeting_step {
            let stats = bidirectional_search(config.n, config.target, meeting_step)?;
            println!(
                "{} n={} u_count={} minimum_u={:?} meeting_step={} forward_states={} backward_states={} reverse_candidates={}",
                if stats.minimum_u.is_some() { "SAT" } else { "UNSAT" },
                config.n,
                config.target,
                stats.minimum_u,
                stats.meeting_step,
                stats.forward_state_counts.last().copied().unwrap_or(0),
                stats.backward_state_counts.last().map_or(0, |(_, count)| *count),
                stats.reverse_candidates,
            );
            if config.per_step {
                for (step, count) in stats.forward_state_counts.iter().enumerate() {
                    println!("direction=forward step={step} states={count}");
                }
                for &(step, count) in &stats.backward_state_counts {
                    println!("direction=backward step={step} states={count}");
                }
            }
        } else {
            let stats = search_with_options(
                config.n,
                config.target,
                SearchOptions {
                    checkpoint: config.checkpoint.as_deref(),
                    resume: config.resume,
                    progress: config.progress,
                    pruning: config.pruning,
                    dump_step: config.dump_step,
                    dump_out: config.dump_out.as_deref(),
                },
            )?;
            println!(
                "{} n={} u_count={} pruning={:?} minimum_u={:?} peak_states={} transitions={} mirror_merges={} geometry_prunes={} closure_prunes={} elapsed_seconds={:.3} peak_rss_kib={}",
                if stats.feasible { "SAT" } else { "UNSAT" },
                config.n,
                config.target,
                config.pruning,
                stats.minimum_u,
                stats.peak_states,
                stats.generated_transitions,
                stats.mirror_merges,
                stats.geometry_prunes,
                stats.closure_prunes,
                stats.elapsed.as_secs_f64(),
                stats
                    .peak_rss_kib
                    .map_or("unknown".into(), |value| value.to_string())
            );
            if config.per_step {
                for (step, count) in stats.state_counts.iter().enumerate() {
                    println!(
                        "step={} states={count}",
                        stats.state_count_start + step
                    );
                }
            }
        }
        Ok(())
    });
    if let Err(error) = result {
        eprintln!("error: {error}");
        process::exit(2);
    }
}

pub fn centered_product_entry() -> Result<(), String> {
    let args: Vec<String> = env::args().skip(1).collect();
    let mut n = 11usize;
    let mut target = 72usize;
    let mut side = None;
    let mut progress = false;
    let mut per_step = false;
    let mut witness_out = None;
    let mut at = 0;
    while at < args.len() {
        match args[at].as_str() {
            "--progress" => {
                progress = true;
                at += 1;
            }
            "--per-step" => {
                per_step = true;
                at += 1;
            }
            "--n" | "--u-count" | "--side" | "--witness-out" => {
                let flag = args[at].as_str();
                let value = args
                    .get(at + 1)
                    .ok_or_else(|| format!("missing value for {flag}"))?;
                match flag {
                    "--n" => n = value.parse().map_err(|_| "invalid --n")?,
                    "--u-count" => target = value.parse().map_err(|_| "invalid --u-count")?,
                    "--side" => side = Some(value.parse().map_err(|_| "invalid --side")?),
                    "--witness-out" => witness_out = Some(PathBuf::from(value)),
                    _ => unreachable!(),
                }
                at += 2;
            }
            "--help" | "-h" => {
                println!(
                    "Usage: search_n11_centered_product --side S [options]\n\
                     Exact finite scope: one centered square in one n x n pattern, exact U count,\n\
                     and global dual connectivity. Defaults: --n 11 --u-count 72.\n\
                     Options: --n N --u-count K --progress --per-step --witness-out PATH"
                );
                return Ok(());
            }
            option => return Err(format!("unknown option {option:?}")),
        }
    }
    let side = side.ok_or("--side is required; this search covers exactly one selected side")?;
    let thresholds = CenteredThresholds {
        repeated_components: 4,
        maximum_cyclic_runs: 3,
        compressed_runs: 9,
    };
    let mut stats = centered_product_search(n, target, side, thresholds, progress, false)?;
    if stats.violation_flags != 0 {
        if progress {
            eprintln!("centered_product witness_recovery=second_exact_pass");
        }
        let witness_pass = centered_product_search(n, target, side, thresholds, progress, true)?;
        stats.witness_rows = witness_pass.witness_rows;
    }
    if let Some(rows) = &stats.witness_rows {
        verify_centered_witness(n, target, side, thresholds, rows)?;
    }
    if let (Some(path), Some(rows)) = (&witness_out, &stats.witness_rows) {
        write_centered_witness(path, n, rows)?;
    }
    println!(
        "CENTERED_PRODUCT n={n} u_count={target} side={side} connected={} any_violation={} repeated_components_gt_4={} maximum_cyclic_runs_gt_3={} compressed_runs_gt_9={} peak_states={} transitions={} equivalent_merges={} elapsed_seconds={:.3} witness={}",
        stats.connected,
        stats.violation_flags != 0,
        stats.violation_flags & 1 != 0,
        stats.violation_flags & 2 != 0,
        stats.violation_flags & 4 != 0,
        stats.peak_states,
        stats.generated_transitions,
        stats.equivalent_merges,
        stats.elapsed.as_secs_f64(),
        stats.witness_rows.is_some(),
    );
    if per_step {
        for (step, count) in stats.state_counts.iter().enumerate() {
            println!("step={step} states={count}");
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;

    fn frontier_accepts_mask(n: usize, mask: usize) -> bool {
        let mut state = State::new(0, 0);
        for step in steps(n).unwrap() {
            let chosen = mask & (1 << (step.row * n + step.col)) != 0;
            let Some(next) = advance(state, &step, chosen) else {
                return false;
            };
            state = next;
        }
        true
    }

    fn brute_accepts_mask(n: usize, mask: usize) -> bool {
        let face_count = (n - 1) * (n - 1);
        let out = face_count;
        let mut parent: Vec<usize> = (0..=face_count).collect();
        for step in steps(n).unwrap() {
            let vertex = step.row * n + step.col;
            if mask & (1 << vertex) == 0 {
                continue;
            }
            for edge in step.edges {
                let neighbor = match edge.neighbor {
                    Neighbor::Left => vertex - 1,
                    Neighbor::Up => vertex - n,
                };
                if mask & (1 << neighbor) != 0 {
                    join(&mut parent, edge.a, edge.b);
                }
            }
        }
        let out_root = root(&mut parent, out);
        (0..face_count).all(|node| root(&mut parent, node) == out_root)
    }

    fn brute_feasible(n: usize, target: usize) -> bool {
        (0usize..1usize << (n * n))
            .any(|mask| mask.count_ones() as usize == target && brute_accepts_mask(n, mask))
    }

    fn canonical_labels(slots: usize) -> Vec<u128> {
        fn enumerate(slot: usize, slots: usize, used: usize, packed: u128, result: &mut Vec<u128>) {
            if slot == slots {
                result.push(packed);
                return;
            }
            for label in 0..=used {
                enumerate(
                    slot + 1,
                    slots,
                    used.max(label + 1),
                    packed | ((label as u128) << (LABEL_BITS * slot)),
                    result,
                );
            }
        }

        let mut result = Vec::new();
        enumerate(0, slots, 0, 0, &mut result);
        result
    }

    #[test]
    fn frontier_agrees_with_exhaustive_brute_force_through_n3() {
        for n in 1..=3 {
            for mask in 0..1usize << (n * n) {
                assert_eq!(
                    frontier_accepts_mask(n, mask),
                    brute_accepts_mask(n, mask),
                    "n={n} mask={mask:b}"
                );
            }
            for target in 0..=n * n {
                assert_eq!(
                    search(n, target).unwrap().feasible,
                    brute_feasible(n, target),
                    "n={n} target={target}"
                );
            }
        }
    }

    #[test]
    fn centered_product_agrees_with_complete_n3_brute_force() {
        let thresholds = CenteredThresholds {
            repeated_components: 0,
            maximum_cyclic_runs: 0,
            compressed_runs: 0,
        };
        for target in 0..=9 {
            let mut expected_connected = false;
            let mut expected_flags = 0;
            for mask in 0usize..1 << 9 {
                if mask.count_ones() as usize != target || !brute_accepts_mask(3, mask) {
                    continue;
                }
                expected_connected = true;
                expected_flags |= centered_violation_flags(3, mask as u128, thresholds).unwrap();
            }
            let actual = centered_product_search(3, target, 3, thresholds, false, false).unwrap();
            assert_eq!(actual.connected, expected_connected, "target={target}");
            assert_eq!(actual.violation_flags, expected_flags, "target={target}");
        }
    }

    #[test]
    fn centered_product_uses_compact_exact_trace_payload() {
        assert_eq!(std::mem::size_of::<CenteredProductState>(), 32);
        assert_eq!(std::mem::size_of::<CenteredProductTrace>(), 4);
    }

    fn assert_threshold_automaton_exhaustive(side: usize) {
        let thresholds = CenteredThresholds {
            repeated_components: 1,
            maximum_cyclic_runs: 1,
            compressed_runs: 2,
        };
        let automaton = ThresholdAutomaton::build(side, thresholds, false).unwrap();
        for mask in 0u32..1u32 << (side * side) {
            let mut class = automaton.initial;
            for position in 0..side * side {
                class = automaton.transitions[position][class as usize]
                    [((mask >> position) & 1) as usize];
            }
            assert_eq!(
                automaton.outputs[class as usize],
                centered_violation_flags(side, mask as u128, thresholds).unwrap(),
                "side={side} mask=0x{mask:x}"
            );
        }
    }

    #[test]
    fn threshold_automaton_agrees_with_terminal_monitor_through_side_four() {
        for side in 2..=4 {
            assert_threshold_automaton_exhaustive(side);
        }
    }

    #[test]
    #[ignore = "33,554,432-pattern exhaustive threshold-language control"]
    fn threshold_automaton_agrees_with_terminal_monitor_at_side_five() {
        assert_threshold_automaton_exhaustive(5);
    }

    #[test]
    fn centered_product_complete_n5_and_n8_controls() {
        let thresholds = CenteredThresholds {
            repeated_components: 4,
            maximum_cyclic_runs: 3,
            compressed_runs: 9,
        };
        let n5 = centered_product_search(5, 14, 3, thresholds, false, false).unwrap();
        assert!(n5.connected);
        assert_eq!(n5.violation_flags, 0);

        let n8 = centered_product_search(8, 37, 2, thresholds, false, false).unwrap();
        assert!(n8.connected);
        assert_eq!(n8.violation_flags, 0);
    }

    #[test]
    fn centered_product_recovers_a_checked_witness() {
        let result = centered_product_search(
            3,
            9,
            3,
            CenteredThresholds {
                repeated_components: 0,
                maximum_cyclic_runs: 0,
                compressed_runs: 0,
            },
            false,
            true,
        )
        .unwrap();
        let rows = result.witness_rows.unwrap();
        assert_eq!(rows, [0b111; 3]);
        assert!(frontier_accepts_mask(3, 0x1ff));
        assert_eq!(rows.iter().map(|row| row.count_ones()).sum::<u32>(), 9);
    }

    #[test]
    fn reverse_transitions_are_exact_through_n3() {
        for n in 1..=3 {
            let schedule = steps(n).unwrap();
            for (at, step) in schedule.iter().enumerate() {
                let all_pre_states: Vec<State> = canonical_labels(step.before.len())
                    .into_iter()
                    .flat_map(|labels| (0..1u32 << n).map(move |row_u| State::new(labels, row_u)))
                    .collect();
                let all_post_states = canonical_labels(step.after_indices.len())
                    .into_iter()
                    .flat_map(|labels| (0..1u32 << n).map(move |row_u| State::new(labels, row_u)));
                for post in all_post_states {
                    let expected: HashSet<State> = all_pre_states
                        .iter()
                        .copied()
                        .filter(|&pre| {
                            let chosen = post.row_u() & (1 << step.col) != 0;
                            advance(pre, step, chosen) == Some(post)
                        })
                        .collect();
                    let actual: HashSet<State> =
                        reverse_predecessors(post, step).into_iter().collect();
                    assert_eq!(actual, expected, "n={n} step={at} post={post:?}");
                }
            }
        }
    }

    #[test]
    fn bidirectional_minimum_matches_one_way_and_brute_force_through_n3() {
        for n in 1..=3 {
            let one_way = search(n, n * n).unwrap().minimum_u;
            let brute = (0usize..1usize << (n * n))
                .filter(|&mask| brute_accepts_mask(n, mask))
                .map(|mask| mask.count_ones() as u16)
                .min();
            assert_eq!(one_way, brute, "n={n}");
            for target in 0..=n * n {
                let expected = one_way.filter(|&cost| cost as usize <= target);
                for meeting_step in 0..=n * n {
                    assert_eq!(
                        bidirectional_search(n, target, meeting_step)
                            .unwrap()
                            .minimum_u,
                        expected,
                        "n={n} target={target} meeting_step={meeting_step}"
                    );
                }
            }
        }
    }

    #[test]
    fn residue_two_grammar_classifier_detects_local_and_carrier_defects() {
        let accepted = State::new(canonicalize_labels([0, 1, 2, 3, 4]), 0);
        assert!(!residue_two_grammar_defects(accepted, 5, 5).has(GrammarViolationKind::Combined));

        let motif_010 = State::new(canonicalize_labels([0, 1, 0, 2, 0]), 0);
        assert!(residue_two_grammar_defects(motif_010, 5, 5).has(GrammarViolationKind::Combined));

        let support_hole = State::new(canonicalize_labels([0, 1, 2, 3, 4, 1, 5, 6]), 0);
        assert!(residue_two_grammar_defects(support_hole, 8, 8).has(GrammarViolationKind::Combined));
        assert!(!residue_two_grammar_defects(State::new(0, 0), 1, 8)
            .has(GrammarViolationKind::Combined));
    }

    #[test]
    fn n5_minimum_paths_never_violate_the_combined_grammar() {
        let result =
            grammar_violation_search(5, 14, false, false, GrammarViolationKind::Combined).unwrap();
        assert_eq!(result.minimum_good_u, Some(14));
        assert_eq!(result.minimum_bad_u, None);
    }

    #[test]
    fn n17_schedule_fits_packed_frontier() {
        let schedule = steps(17).unwrap();
        assert_eq!(schedule.len(), 17 * 17);
        assert!(schedule
            .iter()
            .all(|step| step.before.len().max(step.after_indices.len()) <= MAX_BAG));
    }

    #[test]
    fn checkpoint_round_trip_and_resume_match_full_search() {
        let n = 3;
        let target = 5;
        let schedule = steps(n).unwrap();
        let dual_nodes = (n - 1) * (n - 1) + 1;
        let mut states = FastMap::with_hasher(BuildHasherDefault::default());
        states.insert(State::new(0, 0), 0u16);
        let mut transitions = 0;
        let mut peak = states.len();
        for step in &schedule[..n] {
            let entries: Vec<_> = states.into_iter().collect();
            let (next, generated) = extend_chunk(&entries, step, target, dual_nodes);
            states = next;
            transitions += generated;
            peak = peak.max(states.len());
        }

        let path = env::temp_dir().join(format!(
            "grid-graphs-frontier-checkpoint-{}.bin",
            process::id()
        ));
        write_checkpoint(&path, n, target, n, peak, transitions, &states).unwrap();
        let loaded = read_checkpoint(&path, n, target).unwrap();
        assert_eq!(loaded.completed_steps, n);
        assert_eq!(loaded.states, states);

        let resumed = search_with_options(
            n,
            target,
            SearchOptions {
                checkpoint: Some(&path),
                resume: true,
                progress: false,
                pruning: PruningMode::None,
                ..SearchOptions::default()
            },
        )
        .unwrap();
        fs::remove_file(&path).unwrap();
        let full = search(n, target).unwrap();
        assert_eq!(resumed.minimum_u, full.minimum_u);
        assert_eq!(resumed.generated_transitions, full.generated_transitions);
        assert_eq!(resumed.peak_states, full.peak_states);

        write_checkpoint(&path, n, target, n, peak, transitions, &states).unwrap();
        let resumed_mirror = search_with_options(
            n,
            target,
            SearchOptions {
                checkpoint: Some(&path),
                resume: true,
                pruning: PruningMode::Mirror,
                ..SearchOptions::default()
            },
        )
        .unwrap();
        fs::remove_file(&path).unwrap();
        let full_mirror = search_with_options(
            n,
            target,
            SearchOptions {
                pruning: PruningMode::Mirror,
                ..SearchOptions::default()
            },
        )
        .unwrap();
        assert_eq!(resumed_mirror.minimum_u, full_mirror.minimum_u);
        assert_eq!(
            resumed_mirror.generated_transitions,
            full_mirror.generated_transitions
        );
    }

    #[test]
    fn every_pruning_mode_agrees_with_brute_force_through_n3() {
        for n in 1..=3 {
            for target in 0..=n * n {
                let expected = brute_feasible(n, target);
                for pruning in [
                    PruningMode::Mirror,
                    PruningMode::Geometry,
                    PruningMode::Closure,
                    PruningMode::All,
                ] {
                    let result = search_with_options(
                        n,
                        target,
                        SearchOptions {
                            pruning,
                            ..SearchOptions::default()
                        },
                    )
                    .unwrap();
                    assert_eq!(
                        result.feasible, expected,
                        "n={n} target={target} {pruning:?}"
                    );
                }
            }
        }
    }
}
