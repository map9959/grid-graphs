//! Independent primal checks and bounded, explicitly heuristic corpus generation.
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, VecDeque};

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct Board {
    pub n: usize,
    pub preserved: Vec<bool>,
}

impl Board {
    /// Historical witness alphabet: U is a hole; . is preserved.
    /// Blank lines and whole-line # provenance comments are ignored.
    pub fn parse(text: &str) -> Result<Self, String> {
        let rows: Vec<_> = text
            .lines()
            .map(str::trim)
            .filter(|line| !line.is_empty() && !line.starts_with('#'))
            .collect();
        let n = rows.len();
        if n == 0 || n > 128 || rows.iter().any(|r| r.len() != n) {
            return Err("expected a square U/. witness of side 1..=128".into());
        }
        let mut preserved = Vec::with_capacity(n * n);
        for row in rows {
            for ch in row.bytes() {
                preserved.push(match ch {
                    b'.' => true,
                    b'U' => false,
                    _ => return Err("witness alphabet is U (hole), . (preserved)".into()),
                });
            }
        }
        Ok(Self { n, preserved })
    }

    pub fn rows(&self) -> Vec<String> {
        self.preserved
            .chunks(self.n)
            .map(|row| row.iter().map(|&f| if f { '.' } else { 'U' }).collect())
            .collect()
    }

    pub(crate) fn neighbors(&self, v: usize) -> impl Iterator<Item = usize> {
        let n = self.n;
        [
            (v / n > 0).then(|| v - n),
            (v / n + 1 < n).then(|| v + n),
            (v % n > 0).then(|| v - 1),
            (v % n + 1 < n).then(|| v + 1),
        ]
        .into_iter()
        .flatten()
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Observation {
    pub rows: Vec<String>,
    pub features: BTreeMap<String, i64>,
    /// Row-major 3x3 F masks; no rotational quotient or boundary padding.
    pub local_3x3: Vec<u32>,
}

/// Literal graph traversal. No frontier schedule, dual graph, pruning, or search DSU.
pub fn observe(board: &Board) -> Result<Observation, String> {
    let n = board.n;
    if n == 0 || n > 128 || board.preserved.len() != n * n {
        return Err("invalid board dimensions".into());
    }
    let f = board.preserved.iter().filter(|&&x| x).count();
    let mut seen = vec![false; n * n];
    let mut c = 0;
    let mut z = 0;
    let mut edge_twice = 0;
    for start in 0..n * n {
        if seen[start] {
            continue;
        }
        c += 1;
        seen[start] = true;
        let mut queue = VecDeque::from([start]);
        let (mut vertices, mut degrees) = (0, 0);
        while let Some(v) = queue.pop_front() {
            vertices += 1;
            for w in board.neighbors(v) {
                if !(board.preserved[v] || board.preserved[w]) {
                    continue;
                }
                degrees += 1;
                if !seen[w] {
                    seen[w] = true;
                    queue.push_back(w);
                }
            }
        }
        if degrees / 2 != vertices - 1 {
            return Err("primal forced graph contains a cycle".into());
        }
        if vertices == 1 {
            z += 1;
        }
        edge_twice += degrees;
    }
    seen.fill(false);
    let mut r = 0;
    for start in 0..n * n {
        if seen[start] || !board.preserved[start] {
            continue;
        }
        r += 1;
        seen[start] = true;
        let mut queue = VecDeque::from([start]);
        while let Some(v) = queue.pop_front() {
            for w in board.neighbors(v) {
                if board.preserved[w] && !seen[w] {
                    seen[w] = true;
                    queue.push_back(w);
                }
            }
        }
    }
    let b: usize = (0..n * n)
        .filter(|&v| !board.preserved[v])
        .map(|v| 4 - board.neighbors(v).count())
        .sum();
    if 3 * f + r + b + c != n * n + 4 * n {
        return Err("forest ledger mismatch".into());
    }
    let mut features = BTreeMap::new();
    for (name, value) in [
        ("n", n),
        ("vertices", n * n),
        ("f", f),
        ("r", r),
        ("b", b),
        ("c", c),
        ("z", z),
        ("budget", r + b + c),
        ("forced_edges", edge_twice / 2),
    ] {
        features.insert(name.into(), value as i64);
    }
    if n >= 2 && n % 3 == 2 {
        let k = ((n - 2) / 3) as i64;
        features.insert("target".into(), 3 * k * k + 7 * k);
        features.insert("excess".into(), f as i64 - 3 * k * k - 7 * k);
    }
    let mut local_3x3 = vec![0; 512];
    if n >= 3 {
        for y in 0..n - 2 {
            for x in 0..n - 2 {
                let mut mask = 0;
                for dy in 0..3 {
                    for dx in 0..3 {
                        mask |=
                            usize::from(board.preserved[(y + dy) * n + x + dx]) << (3 * dy + dx);
                    }
                }
                local_3x3[mask] += 1;
            }
        }
    }
    Ok(Observation {
        rows: board.rows(),
        features,
        local_3x3,
    })
}

#[derive(Clone)]
pub(crate) struct Forest {
    board: Board,
    parent: Vec<usize>,
    size: Vec<usize>,
}
impl Forest {
    fn empty(n: usize) -> Self {
        Self {
            board: Board {
                n,
                preserved: vec![false; n * n],
            },
            parent: (0..n * n).collect(),
            size: vec![1; n * n],
        }
    }
    fn root(&self, mut v: usize) -> usize {
        while self.parent[v] != v {
            v = self.parent[v];
        }
        v
    }
    /// Check the entire new star before mutating: every new neighbor must
    /// have a distinct component, also distinct from the center's component.
    pub(crate) fn insert(&mut self, v: usize) -> bool {
        if self.board.preserved[v] {
            return true;
        }
        let mut roots = [usize::MAX; 5];
        roots[0] = self.root(v);
        let mut count = 1;
        for w in self.board.neighbors(v) {
            if self.board.preserved[w] {
                continue;
            }
            let rw = self.root(w);
            if roots[..count].contains(&rw) {
                return false;
            }
            roots[count] = rw;
            count += 1;
        }
        let mut root = roots[0];
        for &other in &roots[1..count] {
            let (a, b) = if self.size[root] >= self.size[other] {
                (root, other)
            } else {
                (other, root)
            };
            self.parent[b] = a;
            self.size[a] += self.size[b];
            root = a;
        }
        self.board.preserved[v] = true;
        true
    }
    pub(crate) fn from_board(board: &Board) -> Result<Self, String> {
        let mut forest = Self::empty(board.n);
        for v in 0..board.n * board.n {
            if board.preserved[v] && !forest.insert(v) {
                return Err("infeasible seed".into());
            }
        }
        Ok(forest)
    }

    pub(crate) fn can_insert(&self, v: usize) -> bool {
        if self.board.preserved[v] {
            return true;
        }
        let mut roots = [usize::MAX; 5];
        roots[0] = self.root(v);
        let mut count = 1;
        for w in self
            .board
            .neighbors(v)
            .filter(|&w| !self.board.preserved[w])
        {
            let r = self.root(w);
            if roots[..count].contains(&r) {
                return false;
            }
            roots[count] = r;
            count += 1;
        }
        true
    }
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e3779b97f4a7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
        z ^ (z >> 31)
    }
    fn shuffle(&mut self, values: &mut [usize]) {
        for i in (1..values.len()).rev() {
            let j = (self.next() % (i + 1) as u64) as usize;
            values.swap(i, j);
        }
    }
}

/// Reproducible local search, NOT an exact optimizer or an UNSAT certificate.
/// Returns one independently verified best witness per run, seeded or unseeded.
pub fn sample(
    n: usize,
    iterations: usize,
    seed: u64,
    initial: Option<&Board>,
) -> Result<Observation, String> {
    Ok(sample_trace(n, iterations, seed, initial, None)?.best)
}

#[derive(Default, Serialize)]
pub struct SamplingStats {
    pub initial_greedy_f: usize,
    pub best_f: usize,
    pub final_current_f: usize,
    pub best_improvements: usize,
    pub repair_attempts: usize,
    pub repair_nodes: usize,
    pub repair_successes: usize,
    pub repair_cutoffs: usize,
    pub repair_exhausted: usize,
    pub repairs_by_deletions: BTreeMap<usize, usize>,
    pub iterations_completed: usize,
    pub elapsed_seconds: f64,
    pub first_target_seconds: Option<f64>,
    pub stop_reason: String,
    pub first_target_method: Option<String>,
    pub shuffle_calls: usize,
    pub shuffle_successes: usize,
    pub shuffle_cutoffs: usize,
    pub shuffle_unchanged_skips: usize,
    pub shuffle_tests: u64,
    pub shuffle_seconds: f64,
    pub shuffle_feasible_cores: usize,
    pub shuffle_boundary_tests: usize,
}

#[derive(Serialize)]
pub struct SampleTrace {
    pub best: Observation,
    /// Up to eight distinct visited boards per score, within two of RUN best.
    pub near_optimal: Vec<Observation>,
    pub stats: SamplingStats,
    pub shuffle_gains: Vec<crate::boundary_shuffle::Gain>,
}

fn remember(
    archive: &mut BTreeMap<usize, BTreeMap<Vec<bool>, Board>>,
    board: &Board,
    score: usize,
    best: usize,
) {
    archive.retain(|&f, _| f + 2 >= best);
    if score + 2 >= best {
        let band = archive.entry(score).or_default();
        if band.len() < 8 {
            band.entry(board.preserved.clone())
                .or_insert_with(|| board.clone());
        }
    }
}

/// Comparative sampler. None preserves the v1 random move sequence. Some
/// enables cycle-guided proposals every other non-restart iteration. The
/// per-proposal node budget bounds an exact fixed-addition deletion query;
/// the overall sampling remains heuristic.
pub fn sample_trace(
    n: usize,
    iterations: usize,
    seed: u64,
    initial: Option<&Board>,
    repair_node_limit: Option<usize>,
) -> Result<SampleTrace, String> {
    sample_run(n, iterations, seed, initial, repair_node_limit, None, None)
}

/// Wall-clock-budgeted baseline, stopping at the first target witness. No
/// cycle-guided moves or trap-specific knowledge is used in this control.
pub fn sample_timed(
    initial: &Board,
    seed: u64,
    milliseconds: u64,
    target: usize,
) -> Result<SampleTrace, String> {
    sample_run(
        initial.n,
        usize::MAX,
        seed,
        Some(initial),
        None,
        Some((milliseconds, target)),
        None,
    )
}

pub fn sample_timed_with_shuffle(
    initial: &Board,
    seed: u64,
    milliseconds: u64,
    target: usize,
    policy: crate::boundary_shuffle::Policy,
) -> Result<SampleTrace, String> {
    sample_run(
        initial.n,
        usize::MAX,
        seed,
        Some(initial),
        None,
        Some((milliseconds, target)),
        Some(policy),
    )
}

fn sample_run(
    n: usize,
    iterations: usize,
    seed: u64,
    initial: Option<&Board>,
    repair_node_limit: Option<usize>,
    timed: Option<(u64, usize)>,
    shuffle_policy: Option<crate::boundary_shuffle::Policy>,
) -> Result<SampleTrace, String> {
    if !(1..=15).contains(&n) {
        return Err("sampling is restricted to side 1..=15".into());
    }
    if shuffle_policy.as_ref().is_some_and(|p| p.interval == 0) {
        return Err("shuffle interval must be positive".into());
    }
    let mut rng = Rng(seed);
    let started = std::time::Instant::now();
    let mut current = match initial {
        Some(b) if b.n == n => {
            observe(b)?;
            Forest::from_board(b)?
        }
        Some(_) => return Err("seed size mismatch".into()),
        None => Forest::empty(n),
    };
    let mut order: Vec<_> = (0..n * n).collect();
    if timed
        .is_some_and(|(_, target)| current.board.preserved.iter().filter(|&&f| f).count() >= target)
    {
        let best = observe(&current.board)?;
        let f = best.features["f"] as usize;
        return Ok(SampleTrace {
            best,
            near_optimal: vec![],
            shuffle_gains: vec![],
            stats: SamplingStats {
                initial_greedy_f: f,
                best_f: f,
                final_current_f: f,
                stop_reason: "target_found".into(),
                first_target_seconds: Some(0.0),
                first_target_method: Some("initial".into()),
                elapsed_seconds: started.elapsed().as_secs_f64(),
                ..SamplingStats::default()
            },
        });
    }
    if timed.is_some_and(|(ms, _)| ms == 0) {
        let best = observe(&current.board)?;
        let f = best.features["f"] as usize;
        return Ok(SampleTrace {
            best,
            near_optimal: vec![],
            shuffle_gains: vec![],
            stats: SamplingStats {
                initial_greedy_f: f,
                best_f: f,
                final_current_f: f,
                stop_reason: "time_limit".into(),
                elapsed_seconds: started.elapsed().as_secs_f64(),
                ..SamplingStats::default()
            },
        });
    }
    rng.shuffle(&mut order);
    for &v in &order {
        current.insert(v);
    }
    let mut best = current.clone();
    let mut best_score = best.board.preserved.iter().filter(|&&f| f).count();
    let mut best_visits = 1u64;
    let mut score = best_score;
    let mut stats = SamplingStats {
        initial_greedy_f: score,
        stop_reason: "iteration_limit".into(),
        ..SamplingStats::default()
    };
    let mut archive = BTreeMap::new();
    remember(&mut archive, &current.board, score, best_score);
    let mut last_improvement = 0usize;
    let mut last_exhausted_shuffle: Option<Vec<bool>> = None;
    let mut shuffle_gains = Vec::new();
    if timed.is_some_and(|(_, target)| best_score >= target) {
        stats.first_target_seconds = Some(started.elapsed().as_secs_f64());
        stats.stop_reason = "target_found".into();
        stats.first_target_method = Some("initial_greedy".into());
    }
    for iteration in 0..iterations {
        if stats.first_target_seconds.is_some() {
            break;
        }
        if timed.is_some_and(|(ms, _)| started.elapsed().as_millis() >= u128::from(ms)) {
            stats.stop_reason = "time_limit".into();
            break;
        }
        if let Some(policy) = shuffle_policy.as_ref().filter(|p| {
            iteration % p.interval == 0
                && iteration.saturating_sub(last_improvement) >= p.stagnation
        }) {
            if last_exhausted_shuffle.as_ref() == Some(&best.board.preserved) {
                stats.shuffle_unchanged_skips += 1;
            } else {
                let remaining = timed
                    .map(|(ms, _)| ms.saturating_sub(started.elapsed().as_millis() as u64))
                    .unwrap_or(u64::MAX);
                let result = crate::boundary_shuffle::probe(
                    &best.board,
                    policy.test_limit,
                    policy.time_limit_ms.min(remaining),
                    false,
                )?;
                stats.shuffle_calls += 1;
                stats.shuffle_tests += result.stats.tests;
                stats.shuffle_seconds += result.stats.elapsed_seconds;
                stats.shuffle_feasible_cores += result.stats.feasible_cores;
                stats.shuffle_boundary_tests += result.stats.boundary_tests;
                match result.status {
                    crate::boundary_shuffle::Status::Found => {
                        let gain = result.gain.expect("successful shuffle has a witness");
                        if gain.after.features["f"] != best_score as i64 + 1 {
                            return Err("shuffle did not improve best score by one".into());
                        }
                        let new_board = Board::parse(&gain.after.rows.join("\n"))?;
                        current = Forest::from_board(&new_board)?;
                        best = current.clone();
                        best_score += 1;
                        score = best_score;
                        best_visits = 1;
                        last_improvement = iteration;
                        stats.best_improvements += 1;
                        stats.shuffle_successes += 1;
                        last_exhausted_shuffle = None;
                        remember(&mut archive, &best.board, best_score, best_score);
                        shuffle_gains.push(gain);
                        if timed.is_some_and(|(_, target)| best_score >= target) {
                            stats.first_target_seconds = Some(started.elapsed().as_secs_f64());
                            stats.first_target_method = Some("shuffle".into());
                            stats.stop_reason = "target_found".into();
                            break;
                        }
                    }
                    crate::boundary_shuffle::Status::ExhaustedCandidates => {
                        last_exhausted_shuffle = Some(best.board.preserved.clone())
                    }
                    _ => stats.shuffle_cutoffs += 1,
                }
            }
        }
        if timed.is_some_and(|(ms, _)| started.elapsed().as_millis() >= u128::from(ms)) {
            stats.stop_reason = "time_limit".into();
            break;
        }
        let mut board = current.board.clone();
        let mut repaired = false;
        if let Some(limit) =
            repair_node_limit.filter(|_| iteration % 2 == 1 && iteration % 256 != 255)
        {
            let ranks = crate::exchange_analysis::promotion_ranks(&board);
            let mut candidates: Vec<_> = (0..ranks.len()).collect();
            rng.shuffle(&mut candidates);
            if let Some(&index) = candidates.iter().take(4).min_by_key(|&&i| ranks[i].1) {
                let first = ranks[index].0;
                let mut adds = vec![first];
                if rng.next() % 2 == 0 {
                    // Prefer a nearby second hole, without prescribing a motif.
                    if let Some(second) = candidates.iter().map(|&i| ranks[i].0).find(|&v| {
                        let dx = (v % n).abs_diff(first % n);
                        let dy = (v / n).abs_diff(first / n);
                        v != first && dx + dy <= 4 && !(dx == 1 && dy == 1)
                    }) {
                        adds.push(second);
                    }
                }
                stats.repair_attempts += 1;
                let result = crate::exchange_analysis::repair(&board, &adds, 3, limit)?;
                stats.repair_nodes += result.nodes;
                match result.status {
                    crate::exchange_analysis::RepairStatus::MinimumFound => {
                        stats.repair_successes += 1;
                        let removed = result.deleted.expect("successful repair has deletions");
                        *stats.repairs_by_deletions.entry(removed.len()).or_default() += 1;
                        for v in removed {
                            board.preserved[v] = false;
                        }
                        for v in adds {
                            board.preserved[v] = true;
                        }
                        repaired = true;
                    }
                    crate::exchange_analysis::RepairStatus::Cutoff => stats.repair_cutoffs += 1,
                    crate::exchange_analysis::RepairStatus::NoRepairWithinBudget => {
                        stats.repair_exhausted += 1
                    }
                }
            }
        }
        if iteration % 256 == 255 {
            board.preserved.fill(false);
        } else if !repaired {
            let mut selected: Vec<_> = (0..n * n).filter(|&v| board.preserved[v]).collect();
            rng.shuffle(&mut selected);
            let remove = 1 + (rng.next() % 6) as usize;
            for &v in selected.iter().take(remove) {
                board.preserved[v] = false;
            }
        }
        let mut candidate = Forest::from_board(&board)?;
        rng.shuffle(&mut order);
        for &v in &order {
            candidate.insert(v);
        }
        let next_score = candidate.board.preserved.iter().filter(|&&f| f).count();
        stats.iterations_completed += 1;
        if next_score > best_score {
            last_improvement = iteration + 1;
            stats.best_improvements += 1;
            best_score = next_score;
            best_visits = 1;
            best = candidate.clone();
        } else if next_score == best_score {
            // Reservoir sampling on the best plateau avoids returning the
            // unchanged seed in every run when neutral exchanges exist.
            best_visits += 1;
            if rng.next() % best_visits == 0 {
                best = candidate.clone();
            }
        }
        remember(&mut archive, &candidate.board, next_score, best_score);
        if timed.is_some_and(|(_, target)| best_score >= target) {
            stats.first_target_seconds = Some(started.elapsed().as_secs_f64());
            stats.stop_reason = "target_found".into();
            stats.first_target_method = Some("random".into());
            break;
        }
        // Occasional downhill moves and restarts prevent a single greedy basin
        // from becoming an implicit hard restriction on the corpus.
        if next_score >= score || rng.next() % 32 == 0 || iteration % 256 == 255 {
            current = candidate;
            score = next_score;
        }
    }
    stats.best_f = best_score;
    stats.final_current_f = score;
    stats.elapsed_seconds = started.elapsed().as_secs_f64();
    let near_optimal = archive
        .into_values()
        .flat_map(BTreeMap::into_values)
        .map(|b| observe(&b))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(SampleTrace {
        best: observe(&best.board)?,
        near_optimal,
        stats,
        shuffle_gains,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn failed_shuffle_probes_do_not_change_random_mutation_sequence() {
        let base = sample_trace(5, 500, 91, None, None).unwrap();
        let with = sample_run(
            5,
            500,
            91,
            None,
            None,
            None,
            Some(crate::boundary_shuffle::Policy {
                interval: 1,
                stagnation: 0,
                test_limit: 10000,
                time_limit_ms: 1000,
            }),
        )
        .unwrap();
        assert_eq!(base.best.rows, with.best.rows);
        assert_eq!(base.stats.final_current_f, with.stats.final_current_f);
        assert_eq!(with.stats.iterations_completed, 500);
        assert!(with.stats.shuffle_calls > 0);
        assert_eq!(with.stats.shuffle_successes, 0);
        let cutoff = sample_run(
            5,
            20,
            91,
            None,
            None,
            None,
            Some(crate::boundary_shuffle::Policy {
                interval: 1,
                stagnation: 0,
                test_limit: 0,
                time_limit_ms: 1000,
            }),
        )
        .unwrap();
        assert_eq!(cutoff.stats.shuffle_cutoffs, 20);
        assert_eq!(cutoff.stats.shuffle_unchanged_skips, 0);
    }
    #[test]
    fn integrated_shuffle_emits_a_replayable_gain() {
        let r: crate::neutral_search::Report =
            serde_json::from_str(include_str!("../data/neutral_escape_14.json")).unwrap();
        let b = Board::parse(&r.trace[r.trace.len() - 2].rows.join("\n")).unwrap();
        let result = sample_timed_with_shuffle(
            &b,
            1,
            10_000,
            77,
            crate::boundary_shuffle::Policy {
                interval: 1,
                stagnation: 0,
                test_limit: 100000,
                time_limit_ms: 1000,
            },
        )
        .unwrap();
        assert_eq!(result.best.features["f"], 77);
        assert_eq!(result.stats.first_target_method.as_deref(), Some("shuffle"));
        assert_eq!(result.stats.iterations_completed, 0);
        assert_eq!(result.shuffle_gains.len(), 1);
        crate::neutral_search::replay(&b, &result.shuffle_gains[0].trace, true).unwrap();
        assert!(sample_timed_with_shuffle(
            &b,
            1,
            10,
            77,
            crate::boundary_shuffle::Policy {
                interval: 0,
                ..Default::default()
            }
        )
        .is_err());
    }
    #[test]
    fn timed_baseline_stops_at_target_or_explicit_deadline() {
        let b = Board::parse("UU\nUU").unwrap();
        let zero = sample_timed(&b, 1, 0, 1).unwrap();
        assert_eq!(zero.stats.stop_reason, "time_limit");
        assert_eq!(zero.stats.iterations_completed, 0);
        assert!(zero.stats.first_target_seconds.is_none());
        let found = sample_timed(&b, 1, 1000, 1).unwrap();
        assert_eq!(found.stats.stop_reason, "target_found");
        assert!(found.stats.first_target_seconds.is_some());
        assert!(found.best.features["f"] >= 1);
        let impossible = sample_timed(&b, 1, 2, 5).unwrap();
        assert_eq!(impossible.stats.stop_reason, "time_limit");
        assert!(impossible.stats.first_target_seconds.is_none());
        let ready = Board::parse("..\nUU").unwrap();
        let already = sample_timed(&ready, 1, 0, 2).unwrap();
        assert_eq!(already.stats.stop_reason, "target_found");
        assert_eq!(already.stats.first_target_seconds, Some(0.0));
        assert_eq!(already.stats.iterations_completed, 0);
    }
    #[test]
    fn incremental_matches_literal_graph_for_every_four_square_subset() {
        for mask in 0u32..1 << 16 {
            let b = Board {
                n: 4,
                preserved: (0..16).map(|v| mask & (1 << v) != 0).collect(),
            };
            assert_eq!(
                Forest::from_board(&b).is_ok(),
                observe(&b).is_ok(),
                "{mask:x}"
            );
        }
    }
    #[test]
    fn insertion_tests_center_and_all_neighbor_components() {
        let b = Board::parse("UUUUU\nU.U.U\nUUUUU\nU.UUU\nUUUUU").unwrap();
        let mut f = Forest::from_board(&b).unwrap();
        let before = f.board.clone();
        assert!(!f.insert(3 * 5 + 3));
        assert_eq!(f.board, before);
        observe(&f.board).unwrap();
    }
    #[test]
    fn sampling_is_bounded_deterministic_and_replayable() {
        assert!(sample(17, 0, 1, None).is_err());
        let a = sample(8, 200, 123, None).unwrap();
        let b = sample(8, 200, 123, None).unwrap();
        assert_eq!(a.rows, b.rows);
        let replay = observe(&Board::parse(&a.rows.join("\n")).unwrap()).unwrap();
        assert_eq!(a.features, replay.features);
        assert_eq!(a.local_3x3.iter().sum::<u32>(), 36);
    }

    #[test]
    fn guided_sampling_and_near_optimal_archive_are_valid() {
        let a = sample_trace(5, 100, 42, None, Some(32)).unwrap();
        let b = sample_trace(5, 100, 42, None, Some(32)).unwrap();
        assert_eq!(a.best.rows, b.best.rows);
        assert_eq!(a.stats.repair_attempts, 50);
        assert_eq!(
            a.stats.repair_attempts,
            a.stats.repair_successes + a.stats.repair_cutoffs + a.stats.repair_exhausted
        );
        assert!(a.stats.repair_nodes <= 32 * a.stats.repair_attempts);
        assert!(a.near_optimal.len() <= 24);
        for o in &a.near_optimal {
            assert!(o.features["f"] + 2 >= a.best.features["f"]);
            let actual = observe(&Board::parse(&o.rows.join("\n")).unwrap()).unwrap();
            assert_eq!(actual.features, o.features);
        }
        assert!(sample_trace(17, 0, 1, None, Some(10)).is_err());
    }

    #[test]
    fn trap_14_has_no_gain_after_deleting_at_most_two_original_vertices() {
        let b = Board::parse(include_str!("../data/corpus_trap_14.txt")).unwrap();
        assert_eq!(observe(&b).unwrap().features["f"], 76);
        // Independent direction from cycle-based repair: enumerate deletions
        // first, then ALL feasible insertion prefixes using the DSU kernel.
        // Feasibility is hereditary, so an illegal prefix has no valid extension.
        fn augment(forest: &Forest, holes: &[usize], start: usize, need: usize) -> bool {
            if need == 0 {
                return true;
            }
            if holes.len() - start < need {
                return false;
            }
            for i in start..=holes.len() - need {
                let mut next = forest.clone();
                if next.insert(holes[i]) && augment(&next, holes, i + 1, need - 1) {
                    return true;
                }
            }
            false
        }
        let selected: Vec<_> = (0..196).filter(|&v| b.preserved[v]).collect();
        let holes: Vec<_> = (0..196).filter(|&v| !b.preserved[v]).collect();
        let mut deletions = vec![Vec::new()];
        for (i, &v) in selected.iter().enumerate() {
            deletions.push(vec![v]);
            for &w in &selected[i + 1..] {
                deletions.push(vec![v, w]);
            }
        }
        assert_eq!(deletions.len(), 2927);
        for deleted in deletions {
            let mut reduced = b.clone();
            for &v in &deleted {
                reduced.preserved[v] = false;
            }
            let forest = Forest::from_board(&reduced).unwrap();
            assert!(
                !augment(&forest, &holes, 0, deleted.len() + 1),
                "deletions={deleted:?}"
            );
        }
    }

    #[test]
    fn trap_14_three_deletions_have_no_gain_without_candidate_prefilter() {
        let b = Board::parse(include_str!("../data/corpus_trap_14.txt")).unwrap();
        observe(&b).unwrap();
        // An unfiltered oracle: never call can_insert, never preselect holes.
        // Enumerate feasible prefixes by the original mutating insertion test.
        fn augment(forest: &Forest, holes: &[usize], start: usize, need: usize) -> bool {
            if need == 0 {
                return true;
            }
            if holes.len() - start < need {
                return false;
            }
            for i in start..=holes.len() - need {
                let mut next = forest.clone();
                if next.insert(holes[i]) && augment(&next, holes, i + 1, need - 1) {
                    return true;
                }
            }
            false
        }
        let selected: Vec<_> = (0..196).filter(|&v| b.preserved[v]).collect();
        let holes: Vec<_> = (0..196).filter(|&v| !b.preserved[v]).collect();
        let mut checked = 0;
        for i in 0..selected.len() {
            for j in i + 1..selected.len() {
                for k in j + 1..selected.len() {
                    let mut reduced = b.clone();
                    for v in [selected[i], selected[j], selected[k]] {
                        reduced.preserved[v] = false;
                    }
                    let forest = Forest::from_board(&reduced).unwrap();
                    assert!(
                        !augment(&forest, &holes, 0, 4),
                        "deletion indices={i},{j},{k}"
                    );
                    checked += 1;
                }
            }
        }
        assert_eq!(checked, 70300);
    }
}
