//! Bounded neutral-plateau exploration. Beam pruning never proves nonexistence.
use crate::certificate_corpus::{observe, Board, Forest, Observation};
use crate::deletion_search;
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::time::Instant;

type Bits = [u64; 4];
fn pack(b: &Board) -> Bits {
    let mut bits = [0; 4];
    for (v, &f) in b.preserved.iter().enumerate() {
        if f {
            bits[v / 64] |= 1 << (v % 64);
        }
    }
    bits
}
fn unpack(n: usize, bits: Bits) -> Board {
    Board {
        n,
        preserved: (0..n * n)
            .map(|v| bits[v / 64] & (1 << (v % 64)) != 0)
            .collect(),
    }
}
fn distance(original: Bits, current: Bits) -> usize {
    original
        .iter()
        .zip(current)
        .map(|(&a, b)| (a & !b).count_ones() as usize)
        .sum()
}
fn mix(mut x: u64) -> u64 {
    x = (x ^ (x >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
    x = (x ^ (x >> 27)).wrapping_mul(0x94d049bb133111eb);
    x ^ (x >> 31)
}
fn fingerprint(bits: Bits, seed: u64) -> u64 {
    bits.into_iter().fold(seed, |a, b| mix(a ^ b))
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Config {
    pub mixed: bool,
    pub seed: u64,
    pub time_limit_ms: u64,
    pub node_limit: u64,
    pub state_limit: usize,
    pub beam_width: usize,
    pub max_depth: usize,
    pub pair_draws_per_state: usize,
    pub probe_node_limit: u64,
    pub probe_time_limit_ms: u64,
    pub larger_probe_stride: usize,
    #[serde(default = "enabled")]
    pub use_certified_radius: bool,
}
fn enabled() -> bool {
    true
}
impl Default for Config {
    fn default() -> Self {
        Self {
            mixed: false,
            seed: 20260908,
            time_limit_ms: 60_000,
            node_limit: 200_000_000,
            state_limit: 100_000,
            beam_width: 128,
            max_depth: 12,
            pair_draws_per_state: 64,
            probe_node_limit: 500_000,
            probe_time_limit_ms: 250,
            larger_probe_stride: 8,
            use_certified_radius: true,
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize, Eq, PartialEq)]
pub struct Move {
    pub deleted: Vec<usize>,
    pub added: Vec<usize>,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct TraceStep {
    pub exchange: Move,
    pub rows: Vec<String>,
    pub f: i64,
    pub missing_original_f: usize,
}
#[derive(Default, Debug, Serialize, Deserialize)]
pub struct Stats {
    pub work_nodes: u64,
    pub states_stored: usize,
    pub expanded_started: usize,
    pub expanded_completed: usize,
    pub duplicate_neighbors: u64,
    pub legal_one_neighbors: u64,
    pub legal_pair_neighbors: u64,
    pub pair_draws: u64,
    pub distinct_pair_choices: u64,
    pub probe_attempts: BTreeMap<usize, usize>,
    pub probe_nodes: u64,
    pub probe_cutoffs: usize,
    pub probes_skipped_by_original_bound: usize,
    pub larger_probes_not_selected: usize,
    pub beam_discarded: usize,
    pub maximum_missing_original_f: usize,
    pub elapsed_seconds: f64,
}
#[derive(Debug, Serialize, Deserialize)]
pub struct Layer {
    pub depth: usize,
    pub frontier: usize,
    pub expanded_completed: usize,
    pub new_states: usize,
    pub next_beam: usize,
    pub interrupted: bool,
}
#[derive(Debug, Serialize, Deserialize)]
pub struct Report {
    pub schema: String,
    pub scope: String,
    pub config: Config,
    pub original: Observation,
    pub status: String,
    pub original_excluded_deletion_radius: Option<usize>,
    pub original_bound_source: Option<String>,
    pub stats: Stats,
    pub layers: Vec<Layer>,
    pub trace_kind: String,
    pub trace: Vec<TraceStep>,
    pub endpoint: Observation,
}

struct Node {
    bits: Bits,
    parent: Option<usize>,
    exchange: Move,
    missing: usize,
    shape: [i64; 4], // c,z,r,b; budget itself is constant on this plateau.
    tie: u64,
}

/// The radius-four exclusion is used ONLY for the actual saved input set.
fn known_radius(b: &Board) -> Option<usize> {
    let certified = Board::parse(include_str!("../data/corpus_trap_14.txt")).expect("fixture");
    (b == &certified).then_some(4)
}
fn probe_allowed(radius: Option<usize>, missing: usize, further_deleted: usize) -> bool {
    radius.is_none_or(|r| missing + further_deleted > r)
}

/// Exact replay with literal graph traversal; a final improving move is optional.
pub fn replay(b: &Board, steps: &[TraceStep], escape: bool) -> Result<Observation, String> {
    if !(1..=15).contains(&b.n) {
        return Err("trace board outside supported search dimensions".into());
    }
    let initial = observe(b)?;
    let mut current = b.clone();
    let original = pack(b);
    if escape && steps.is_empty() {
        return Err("escape trace is empty".into());
    }
    for (i, step) in steps.iter().enumerate() {
        let mv = &step.exchange;
        let deleted: BTreeSet<_> = mv.deleted.iter().copied().collect();
        let added: BTreeSet<_> = mv.added.iter().copied().collect();
        if deleted.len() != mv.deleted.len() || added.len() != mv.added.len() {
            return Err("duplicate move vertices".into());
        }
        if deleted
            .iter()
            .any(|&v| v >= current.preserved.len() || !current.preserved[v])
            || added
                .iter()
                .any(|&v| v >= current.preserved.len() || current.preserved[v])
        {
            return Err("move does not delete current F and insert current U".into());
        }
        let last_gain = escape && i + 1 == steps.len();
        if last_gain {
            if added.len() != deleted.len() + 1 || deleted.len() > 2 {
                return Err("invalid gain move".into());
            }
        } else if !(1..=2).contains(&deleted.len()) || added.len() != deleted.len() {
            return Err("invalid neutral move".into());
        }
        for &v in &deleted {
            current.preserved[v] = false;
        }
        for &v in &added {
            current.preserved[v] = true;
        }
        let o = observe(&current)?;
        if o.features["f"] != initial.features["f"] + i64::from(last_gain)
            || o.features["f"] != step.f
            || o.rows != step.rows
            || distance(original, pack(&current)) != step.missing_original_f
        {
            return Err("trace snapshot or score mismatch".into());
        }
    }
    observe(&current)
}

#[derive(Debug)]
enum Stop {
    Nodes,
    Time,
    States,
}
impl Stop {
    fn label(&self) -> &'static str {
        match self {
            Self::Nodes => "node_limit",
            Self::Time => "time_limit",
            Self::States => "state_limit",
        }
    }
}
struct Engine {
    original: Board,
    original_bits: Bits,
    score: i64,
    radius: Option<usize>,
    cfg: Config,
    started: Instant,
    rng: u64,
    nodes: Vec<Node>,
    seen: HashMap<Bits, usize>,
    stats: Stats,
    representative: usize,
}
impl Engine {
    fn new(b: &Board, cfg: Config) -> Result<Self, String> {
        if !(1..=15).contains(&b.n) {
            return Err("neutral search restricted to side 1..=15".into());
        }
        if cfg.state_limit == 0
            || cfg.beam_width == 0
            || cfg.beam_width > cfg.state_limit
            || cfg.larger_probe_stride == 0
            || cfg.max_depth > 64
        {
            return Err("invalid state/beam/depth/probe limits".into());
        }
        let o = observe(b)?;
        let bits = pack(b);
        let seed = cfg.seed;
        let root = Node {
            bits,
            parent: None,
            exchange: Move {
                deleted: vec![],
                added: vec![],
            },
            missing: 0,
            shape: [
                o.features["c"],
                o.features["z"],
                o.features["r"],
                o.features["b"],
            ],
            tie: fingerprint(bits, seed),
        };
        Ok(Self {
            original: b.clone(),
            original_bits: bits,
            score: o.features["f"],
            radius: if cfg.use_certified_radius {
                known_radius(b)
            } else {
                None
            },
            cfg,
            started: Instant::now(),
            rng: seed,
            nodes: vec![root],
            seen: HashMap::from([(bits, 0)]),
            stats: Stats::default(),
            representative: 0,
        })
    }
    fn check(&self) -> Result<(), Stop> {
        if self.stats.work_nodes >= self.cfg.node_limit {
            return Err(Stop::Nodes);
        }
        if self.started.elapsed().as_millis() >= u128::from(self.cfg.time_limit_ms) {
            return Err(Stop::Time);
        }
        Ok(())
    }
    fn tick(&mut self) -> Result<(), Stop> {
        self.check()?;
        self.stats.work_nodes += 1;
        Ok(())
    }
    fn board(&self, id: usize) -> Board {
        unpack(self.original.n, self.nodes[id].bits)
    }
    fn add(&mut self, parent: usize, b: Board, exchange: Move) -> Result<Option<usize>, Stop> {
        let bits = pack(&b);
        if self.seen.contains_key(&bits) {
            self.stats.duplicate_neighbors += 1;
            return Ok(None);
        }
        if self.nodes.len() >= self.cfg.state_limit {
            return Err(Stop::States);
        }
        let o = observe(&b).expect("generated neutral state failed independent validation");
        assert_eq!(o.features["f"], self.score);
        let missing = distance(self.original_bits, bits);
        let id = self.nodes.len();
        self.nodes.push(Node {
            bits,
            parent: Some(parent),
            exchange,
            missing,
            shape: [
                o.features["c"],
                o.features["z"],
                o.features["r"],
                o.features["b"],
            ],
            tie: fingerprint(bits, self.cfg.seed),
        });
        self.seen.insert(bits, id); // Full 256-bit equality, not hash equality.
        if missing > self.nodes[self.representative].missing {
            self.representative = id;
        }
        self.stats.maximum_missing_original_f = self.stats.maximum_missing_original_f.max(missing);
        Ok(Some(id))
    }
    fn expand(&mut self, id: usize) -> Result<Vec<usize>, Stop> {
        let b = self.board(id);
        let selected: Vec<_> = (0..b.n * b.n).filter(|&v| b.preserved[v]).collect();
        let holes: Vec<_> = (0..b.n * b.n).filter(|&v| !b.preserved[v]).collect();
        let mut children = Vec::new();
        // Enumerate every one-for-one neighbor, not the first repair per hole.
        for &v in &selected {
            self.tick()?;
            let mut reduced = b.clone();
            reduced.preserved[v] = false;
            let forest = Forest::from_board(&reduced).expect("deletion preserves a forest");
            for &w in &holes {
                self.tick()?;
                if !forest.can_insert(w) {
                    continue;
                }
                self.stats.legal_one_neighbors += 1;
                reduced.preserved[w] = true;
                if let Some(child) = self.add(
                    id,
                    reduced.clone(),
                    Move {
                        deleted: vec![v],
                        added: vec![w],
                    },
                )? {
                    children.push(child);
                }
                reduced.preserved[w] = false;
            }
        }
        if self.cfg.mixed && selected.len() >= 2 {
            let mut pairs = BTreeSet::new();
            for _ in 0..self.cfg.pair_draws_per_state {
                self.tick()?;
                self.stats.pair_draws += 1;
                self.rng = self.rng.wrapping_add(0x9e3779b97f4a7c15);
                let i = (mix(self.rng) % selected.len() as u64) as usize;
                self.rng = self.rng.wrapping_add(0x9e3779b97f4a7c15);
                let j = (mix(self.rng) % (selected.len() - 1) as u64) as usize;
                let j = if j >= i { j + 1 } else { j };
                pairs.insert((i.min(j), i.max(j)));
            }
            self.stats.distinct_pair_choices += pairs.len() as u64;
            for (i, j) in pairs {
                self.tick()?;
                let mut reduced = b.clone();
                reduced.preserved[selected[i]] = false;
                reduced.preserved[selected[j]] = false;
                let forest = Forest::from_board(&reduced).expect("deletion preserves forest");
                let mut eligible = Vec::new();
                for &w in &holes {
                    self.tick()?;
                    if forest.can_insert(w) {
                        eligible.push(w);
                    }
                }
                for a in 0..eligible.len() {
                    let mut prefix = forest.clone();
                    assert!(prefix.insert(eligible[a]));
                    for &w in &eligible[a + 1..] {
                        self.tick()?;
                        if !prefix.can_insert(w) {
                            continue;
                        }
                        self.stats.legal_pair_neighbors += 1;
                        reduced.preserved[eligible[a]] = true;
                        reduced.preserved[w] = true;
                        if let Some(child) = self.add(
                            id,
                            reduced.clone(),
                            Move {
                                deleted: vec![selected[i], selected[j]],
                                added: vec![eligible[a], w],
                            },
                        )? {
                            children.push(child);
                        }
                        reduced.preserved[eligible[a]] = false;
                        reduced.preserved[w] = false;
                    }
                }
            }
        }
        Ok(children)
    }
    fn probe(&mut self, id: usize) -> Result<Option<Move>, Stop> {
        let b = self.board(id);
        for j in 0..=2 {
            if !probe_allowed(self.radius, self.nodes[id].missing, j) {
                self.stats.probes_skipped_by_original_bound += 1;
                continue;
            }
            // Single additions are always checked when permitted. Probe one
            // deletion at distance four (or beyond); larger probes only on
            // a deterministic subset of retained states.
            if j == 2 && id % self.cfg.larger_probe_stride != 0 {
                self.stats.larger_probes_not_selected += 1;
                continue;
            }
            self.check()?;
            let remaining_ms = self
                .cfg
                .time_limit_ms
                .saturating_sub(self.started.elapsed().as_millis() as u64);
            if remaining_ms == 0 {
                return Err(Stop::Time);
            }
            let allowance =
                (self.cfg.node_limit - self.stats.work_nodes).min(self.cfg.probe_node_limit);
            *self.stats.probe_attempts.entry(j).or_default() += 1;
            let result = deletion_search::search(
                &b,
                j,
                allowance,
                remaining_ms.min(self.cfg.probe_time_limit_ms),
            )
            .expect("validated bounded probe input");
            self.stats.probe_nodes += result.nodes;
            self.stats.work_nodes += result.nodes;
            match result.status {
                deletion_search::Status::ImprovingExchangeFound => {
                    return Ok(Some(Move {
                        deleted: result.deleted.unwrap(),
                        added: result.added.unwrap(),
                    }))
                }
                deletion_search::Status::ExhaustedNeighborhood => (),
                _ => self.stats.probe_cutoffs += 1,
            }
        }
        Ok(None)
    }
    fn beam(&mut self, mut candidates: Vec<usize>) -> Vec<usize> {
        if candidates.len() <= self.cfg.beam_width {
            return candidates;
        }
        let total = candidates.len();
        let quota = self.cfg.beam_width / 3;
        let mut chosen = BTreeSet::new();
        let mut result = Vec::new();
        candidates.sort_by_key(|&id| {
            (
                std::cmp::Reverse(self.nodes[id].missing),
                self.nodes[id].tie,
                id,
            )
        });
        for &id in candidates.iter().take(quota) {
            chosen.insert(id);
            result.push(id);
        }
        let mut buckets = BTreeMap::<[i64; 4], Vec<usize>>::new();
        for &id in candidates.iter().rev() {
            buckets.entry(self.nodes[id].shape).or_default().push(id);
        }
        while result.len() < 2 * quota {
            let before = result.len();
            for bucket in buckets.values_mut() {
                while let Some(id) = bucket.pop() {
                    if chosen.insert(id) {
                        result.push(id);
                        break;
                    }
                }
                if result.len() >= 2 * quota {
                    break;
                }
            }
            if result.len() == before {
                break;
            }
        }
        candidates.sort_by_key(|&id| (self.nodes[id].tie, id));
        for id in candidates {
            if result.len() >= self.cfg.beam_width {
                break;
            }
            if chosen.insert(id) {
                result.push(id);
            }
        }
        self.stats.beam_discarded += total - result.len();
        result
    }
    fn trace(&self, mut id: usize, gain: Option<Move>) -> Vec<TraceStep> {
        let mut moves = Vec::new();
        while let Some(parent) = self.nodes[id].parent {
            moves.push(self.nodes[id].exchange.clone());
            id = parent;
        }
        moves.reverse();
        if let Some(m) = gain {
            moves.push(m);
        }
        let mut b = self.original.clone();
        moves
            .into_iter()
            .map(|exchange| {
                for &v in &exchange.deleted {
                    b.preserved[v] = false;
                }
                for &v in &exchange.added {
                    b.preserved[v] = true;
                }
                TraceStep {
                    f: b.preserved.iter().filter(|&&f| f).count() as i64,
                    rows: b.rows(),
                    missing_original_f: distance(self.original_bits, pack(&b)),
                    exchange,
                }
            })
            .collect()
    }
    fn finish(mut self, status: &str, layers: Vec<Layer>, id: usize, gain: Option<Move>) -> Report {
        let escape = gain.is_some();
        let trace = self.trace(id, gain);
        let endpoint =
            replay(&self.original, &trace, escape).expect("trace failed independent replay");
        self.stats.states_stored = self.nodes.len();
        self.stats.elapsed_seconds = self.started.elapsed().as_secs_f64();
        Report { schema:"grid-graphs.neutral-plateau.v1".into(),
            scope:"bounded beam exploration, not exhaustive plateau coverage or shortest-path certification; vertices are row-major zero-based".into(),
            original:observe(&self.original).unwrap(), config:self.cfg, status:status.into(),
            original_excluded_deletion_radius:self.radius,
            original_bound_source:self.radius.map(|_| "data/corpus_trap_14_four_for_five.json plus completed smaller neighborhoods".into()),
            stats:self.stats, layers, trace_kind:if escape {"escape"} else {"neutral_representative"}.into(), trace, endpoint }
    }
}

pub fn search(b: &Board, cfg: Config) -> Result<Report, String> {
    let mut e = Engine::new(b, cfg)?;
    let mut frontier = vec![0];
    let mut layers = Vec::new();
    for depth in 0..=e.cfg.max_depth {
        let mut next = Vec::new();
        let start_nodes = e.nodes.len();
        let start_expanded = e.stats.expanded_completed;
        let mut layer = Layer {
            depth,
            frontier: frontier.len(),
            expanded_completed: 0,
            new_states: 0,
            next_beam: 0,
            interrupted: false,
        };
        for &id in &frontier {
            let mut gain = None;
            let result = (|| {
                e.check()?;
                gain = e.probe(id)?;
                if gain.is_none() && depth < e.cfg.max_depth {
                    e.stats.expanded_started += 1;
                    next.extend(e.expand(id)?);
                    e.stats.expanded_completed += 1;
                }
                Ok::<(), Stop>(())
            })();
            if result.is_err() || gain.is_some() {
                layer.expanded_completed = e.stats.expanded_completed - start_expanded;
                layer.new_states = e.nodes.len() - start_nodes;
                layer.interrupted = true;
                layers.push(layer);
                if let Some(m) = gain {
                    return Ok(e.finish("escape_found", layers, id, Some(m)));
                }
                let status = result.unwrap_err().label();
                let representative = e.representative;
                return Ok(e.finish(status, layers, representative, None));
            }
        }
        layer.expanded_completed = e.stats.expanded_completed - start_expanded;
        layer.new_states = e.nodes.len() - start_nodes;
        if depth == e.cfg.max_depth || next.is_empty() {
            layers.push(layer);
            let representative = e.representative;
            let status = if depth == e.cfg.max_depth {
                "depth_limit"
            } else {
                "frontier_empty"
            };
            return Ok(e.finish(status, layers, representative, None));
        }
        frontier = e.beam(next);
        layer.next_beam = frontier.len();
        layers.push(layer);
    }
    unreachable!()
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn full_board_keys_round_trip_through_every_supported_bit() {
        let mut keys = BTreeSet::new();
        for v in 0..225 {
            let mut b = Board {
                n: 15,
                preserved: vec![false; 225],
            };
            b.preserved[v] = true;
            let key = pack(&b);
            assert_eq!(unpack(15, key), b);
            assert!(keys.insert(key));
        }
        assert_eq!(keys.len(), 225);
    }
    #[test]
    fn exact_one_neighbors_match_every_feasible_three_square_board() {
        for mask in 0u32..512 {
            let b = Board {
                n: 3,
                preserved: (0..9).map(|v| mask & (1 << v) != 0).collect(),
            };
            if observe(&b).is_err() {
                continue;
            }
            let mut e = Engine::new(&b, Config::default()).unwrap();
            let children = e.expand(0).unwrap();
            let actual: BTreeSet<_> = children.iter().map(|&id| e.nodes[id].bits).collect();
            let mut expected = BTreeSet::new();
            for v in 0..9 {
                for w in 0..9 {
                    if !b.preserved[v] || b.preserved[w] {
                        continue;
                    }
                    let mut next = b.clone();
                    next.preserved[v] = false;
                    next.preserved[w] = true;
                    if observe(&next).is_ok() {
                        expected.insert(pack(&next));
                    }
                }
            }
            assert_eq!(actual, expected, "mask={mask}");
            assert!(e.expand(0).unwrap().is_empty()); // Exact-state duplicate handling.
        }
    }
    #[test]
    fn fixture_pruning_is_identity_bound_and_uses_actual_distance() {
        let b = Board::parse(include_str!("../data/corpus_trap_14.txt")).unwrap();
        assert_eq!(known_radius(&b), Some(4));
        let mut different = b.clone();
        different.preserved[0] = false;
        assert_eq!(known_radius(&different), None);
        assert!(!probe_allowed(Some(4), 3, 1));
        assert!(probe_allowed(Some(4), 3, 2));
        assert!(!probe_allowed(Some(4), 4, 0));
        assert!(probe_allowed(Some(4), 5, 0));
        assert!(probe_allowed(None, 0, 0));
        let engine = Engine::new(
            &b,
            Config {
                use_certified_radius: false,
                ..Config::default()
            },
        )
        .unwrap();
        assert_eq!(engine.radius, None);
    }
    #[test]
    fn beam_limits_and_trace_replay_are_explicit() {
        let b = Board::parse("..\nUU").unwrap();
        let full = search(
            &b,
            Config {
                max_depth: 10,
                ..Config::default()
            },
        )
        .unwrap();
        assert_eq!(full.status, "frontier_empty");
        assert_eq!(full.stats.states_stored, 4);
        assert_eq!(full.stats.beam_discarded, 0);
        let narrow = search(
            &b,
            Config {
                beam_width: 1,
                ..Config::default()
            },
        )
        .unwrap();
        assert!(narrow.stats.beam_discarded > 0);
        let capped = search(
            &b,
            Config {
                state_limit: 1,
                beam_width: 1,
                ..Config::default()
            },
        )
        .unwrap();
        assert_eq!(capped.status, "state_limit");
        assert_eq!(capped.stats.states_stored, 1);
        assert_eq!(
            search(
                &b,
                Config {
                    node_limit: 0,
                    ..Config::default()
                }
            )
            .unwrap()
            .status,
            "node_limit"
        );
        assert_eq!(
            search(
                &b,
                Config {
                    time_limit_ms: 0,
                    ..Config::default()
                }
            )
            .unwrap()
            .status,
            "time_limit"
        );
        assert_eq!(
            search(
                &b,
                Config {
                    max_depth: 0,
                    ..Config::default()
                }
            )
            .unwrap()
            .status,
            "depth_limit"
        );
        let empty = Board::parse("UU\nUU").unwrap();
        let mut escaped = search(&empty, Config::default()).unwrap();
        assert_eq!(escaped.status, "escape_found");
        assert_eq!(
            replay(&empty, &escaped.trace, true).unwrap().features["f"],
            1
        );
        let repeated = escaped.trace[0].exchange.added[0];
        escaped.trace[0].exchange.added.push(repeated);
        assert!(replay(&empty, &escaped.trace, true).is_err());
    }
    #[test]
    fn mixed_moves_are_neutral_and_deterministic() {
        let b = Board::parse("...\nUUU\nUUU").unwrap();
        let cfg = Config {
            mixed: true,
            seed: 7,
            pair_draws_per_state: 100,
            ..Config::default()
        };
        let mut a = Engine::new(&b, cfg.clone()).unwrap();
        let mut c = Engine::new(&b, cfg).unwrap();
        let aa = a.expand(0).unwrap();
        let cc = c.expand(0).unwrap();
        assert_eq!(
            aa.iter().map(|&id| a.nodes[id].bits).collect::<Vec<_>>(),
            cc.iter().map(|&id| c.nodes[id].bits).collect::<Vec<_>>()
        );
        assert!(a.stats.legal_pair_neighbors > 0);
        // With this seed, 100 draws cover all three possible deletion pairs.
        // Check every resulting two-for-two neighbor against literal boards.
        let actual_pairs: BTreeSet<_> = aa
            .iter()
            .filter(|&&id| a.nodes[id].exchange.deleted.len() == 2)
            .map(|&id| a.nodes[id].bits)
            .collect();
        let expected_pairs: BTreeSet<_> = (0u32..512)
            .filter_map(|mask| {
                if (7u32 & !mask).count_ones() != 2 || (mask & !7u32).count_ones() != 2 {
                    return None;
                }
                let candidate = Board {
                    n: 3,
                    preserved: (0..9).map(|v| mask & (1 << v) != 0).collect(),
                };
                observe(&candidate).is_ok().then(|| pack(&candidate))
            })
            .collect();
        assert_eq!(actual_pairs, expected_pairs);
        for id in aa {
            replay(&b, &a.trace(id, None), false).unwrap();
        }
        let big = Board {
            n: 17,
            preserved: vec![false; 289],
        };
        assert!(search(&big, Config::default()).is_err());
    }

    #[test]
    fn archived_escape_replays_all_neutral_steps_and_final_gain() {
        let report: Report =
            serde_json::from_str(include_str!("../data/neutral_escape_14.json")).unwrap();
        let b = Board::parse(&report.original.rows.join("\n")).unwrap();
        assert_eq!(report.status, "escape_found");
        assert_eq!(report.trace.len(), 12);
        assert!(report.trace[..11]
            .iter()
            .all(|s| s.f == 76 && s.exchange.deleted.len() == 1 && s.exchange.added.len() == 1));
        let endpoint = replay(&b, &report.trace, true).unwrap();
        assert_eq!(endpoint.features["f"], 77);
        assert_eq!(endpoint.rows, report.endpoint.rows);
        assert_eq!(report.trace.last().unwrap().missing_original_f, 9);
        let mut bad = report.trace.clone();
        bad[1].exchange.deleted[0] = bad[0].exchange.deleted[0];
        assert!(replay(&b, &bad, true).is_err());
    }
}
