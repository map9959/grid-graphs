//! Physical blocking paths and node-bounded exact deletion repair.
use crate::certificate_corpus::{observe, Board, Observation};
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet, HashSet, VecDeque};

#[derive(Serialize)]
pub struct EdgeCut {
    pub edge: [usize; 2],
    /// ALL these original F endpoints must be deleted to remove this edge.
    pub must_delete: Vec<usize>,
}
#[derive(Serialize)]
pub struct BlockingPath {
    pub terminals: [usize; 2],
    pub vertices: Vec<usize>,
    pub removable_edges: Vec<EdgeCut>,
}
#[derive(Serialize)]
pub struct Promotion {
    pub vertex: usize,
    pub xy: [usize; 2],
    pub new_neighbors: Vec<usize>,
    pub terminals_by_component: BTreeMap<usize, Vec<usize>>,
    pub cycle_rank: usize,
    pub blocking_paths: Vec<BlockingPath>,
    /// Number of displayed basis paths cut by deleting this vertex alone.
    /// Covering this basis is necessary, NOT sufficient for a repair.
    pub single_deletion_path_hits: BTreeMap<usize, usize>,
}
#[derive(Serialize)]
pub struct Diagnostics {
    pub schema: &'static str,
    pub scope: &'static str,
    pub vertex_numbering: &'static str,
    pub observation: Observation,
    pub component_sizes: Vec<usize>,
    pub isolated_vertices: Vec<usize>,
    pub promotion_cycle_rank_histogram: BTreeMap<usize, usize>,
    pub promotions: Vec<Promotion>,
}

struct Trees {
    parent: Vec<usize>,
    depth: Vec<usize>,
    component: Vec<usize>,
    sizes: Vec<usize>,
}
impl Trees {
    fn new(b: &Board) -> Self {
        let mut t = Self {
            parent: vec![usize::MAX; b.n * b.n],
            depth: vec![0; b.n * b.n],
            component: vec![0; b.n * b.n],
            sizes: Vec::new(),
        };
        for start in 0..b.n * b.n {
            if t.parent[start] != usize::MAX {
                continue;
            }
            let label = t.sizes.len();
            let mut size = 0;
            t.parent[start] = start;
            let mut queue = VecDeque::from([start]);
            while let Some(v) = queue.pop_front() {
                size += 1;
                t.component[v] = label;
                for w in b.neighbors(v) {
                    if (b.preserved[v] || b.preserved[w]) && t.parent[w] == usize::MAX {
                        t.parent[w] = v;
                        t.depth[w] = t.depth[v] + 1;
                        queue.push_back(w);
                    }
                }
            }
            t.sizes.push(size);
        }
        t
    }
    fn path(&self, mut a: usize, mut b: usize) -> Vec<usize> {
        let (mut left, mut right) = (vec![a], vec![b]);
        while a != b {
            if self.depth[a] >= self.depth[b] {
                a = self.parent[a];
                left.push(a);
            } else {
                b = self.parent[b];
                right.push(b);
            }
        }
        right.pop();
        left.extend(right.into_iter().rev());
        left
    }
}

pub fn diagnose(b: &Board) -> Result<Diagnostics, String> {
    let observation = observe(b)?;
    if b.n > 32 {
        return Err("path diagnostics are restricted to side 32 or below".into());
    }
    let trees = Trees::new(b);
    let mut promotions = Vec::new();
    let mut histogram = BTreeMap::new();
    for v in 0..b.n * b.n {
        if b.preserved[v] {
            continue;
        }
        let new_neighbors: Vec<_> = b.neighbors(v).filter(|&w| !b.preserved[w]).collect();
        let mut groups: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
        for &w in std::iter::once(&v).chain(new_neighbors.iter()) {
            groups.entry(trees.component[w]).or_default().push(w);
        }
        let cycle_rank = new_neighbors.len() + 1 - groups.len();
        *histogram.entry(cycle_rank).or_insert(0) += 1;
        let mut paths = Vec::new();
        let mut hits = BTreeMap::new();
        for group in groups.values() {
            for &w in &group[1..] {
                let vertices = trees.path(group[0], w);
                let mut removable_edges = Vec::new();
                let mut single_cuts = BTreeSet::new();
                for edge in vertices.windows(2) {
                    // A promoted vertex keeps ALL its incident edges forced,
                    // even when an original F neighbor is deleted.
                    if edge.contains(&v) {
                        continue;
                    }
                    let must_delete: Vec<_> =
                        edge.iter().copied().filter(|&u| b.preserved[u]).collect();
                    if must_delete.len() == 1 {
                        single_cuts.insert(must_delete[0]);
                    }
                    removable_edges.push(EdgeCut {
                        edge: [edge[0], edge[1]],
                        must_delete,
                    });
                }
                for u in single_cuts {
                    *hits.entry(u).or_insert(0) += 1;
                }
                paths.push(BlockingPath {
                    terminals: [group[0], w],
                    vertices,
                    removable_edges,
                });
            }
        }
        promotions.push(Promotion {
            vertex: v,
            xy: [v % b.n, v / b.n],
            new_neighbors,
            terminals_by_component: groups,
            cycle_rank,
            blocking_paths: paths,
            single_deletion_path_hits: hits,
        });
    }
    let isolated_vertices = (0..b.n * b.n)
        .filter(|&v| trees.sizes[trees.component[v]] == 1)
        .collect();
    Ok(Diagnostics {
        schema: "grid-graphs.exchange-diagnostics.v1",
        scope: "fixed witness diagnostics; no deletion search or optimality claim",
        vertex_numbering: "row-major zero-based: vertex=y*n+x",
        observation,
        component_sizes: trees.sizes,
        isolated_vertices,
        promotion_cycle_rank_histogram: histogram,
        promotions,
    })
}

/// Cheap component-aware proposal scores for an already validated forest.
pub(crate) fn promotion_ranks(b: &Board) -> Vec<(usize, usize)> {
    let trees = Trees::new(b);
    (0..b.n * b.n)
        .filter(|&v| !b.preserved[v])
        .map(|v| {
            let mut labels = [usize::MAX; 5];
            labels[0] = trees.component[v];
            let (mut distinct, mut edges) = (1, 0);
            for w in b.neighbors(v).filter(|&w| !b.preserved[w]) {
                edges += 1;
                let label = trees.component[w];
                if !labels[..distinct].contains(&label) {
                    labels[distinct] = label;
                    distinct += 1;
                }
            }
            (v, edges + 1 - distinct)
        })
        .collect()
}

/// Find a physical cycle using a BFS tree and its first non-tree edge.
fn cycle(b: &Board) -> Option<Vec<[usize; 2]>> {
    let t = Trees::new(b);
    for v in 0..b.n * b.n {
        for w in b.neighbors(v) {
            if w <= v || !(b.preserved[v] || b.preserved[w]) {
                continue;
            }
            if t.parent[v] == w || t.parent[w] == v {
                continue;
            }
            let path = t.path(v, w);
            let mut edges: Vec<_> = path.windows(2).map(|e| [e[0], e[1]]).collect();
            edges.push([w, v]);
            return Some(edges);
        }
    }
    None
}

/// Diagnostic length of one detected cycle, not necessarily the shortest.
pub(crate) fn first_cycle_length(b: &Board) -> Option<usize> {
    cycle(b).map(|edges| edges.len())
}

#[derive(Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum RepairStatus {
    MinimumFound,
    NoRepairWithinBudget,
    Cutoff,
}

#[derive(Serialize)]
pub struct Repair {
    pub status: RepairStatus,
    pub additions: Vec<usize>,
    pub max_deletions: usize,
    pub node_limit: usize,
    pub nodes: usize,
    pub ruled_out_budgets_through: Option<usize>,
    pub deleted: Option<Vec<usize>>,
    pub minimum_deletions: Option<usize>,
    pub observation: Option<Observation>,
}

enum Outcome {
    Found(Vec<usize>),
    Exhausted,
    Cutoff,
}
struct Search<'a> {
    original: &'a Board,
    locked: Vec<bool>,
    nodes: usize,
    limit: usize,
    seen: HashSet<[u64; 4]>,
}
impl Search<'_> {
    fn visit(&mut self, board: &mut Board, budget: usize) -> Outcome {
        if self.nodes >= self.limit {
            return Outcome::Cutoff;
        }
        self.nodes += 1;
        let mut key = [0u64; 4];
        for (v, &f) in board.preserved.iter().enumerate() {
            if f {
                key[v / 64] |= 1 << (v % 64);
            }
        }
        if !self.seen.insert(key) {
            return Outcome::Exhausted;
        }
        let Some(edges) = cycle(board) else {
            return Outcome::Found(
                (0..board.n * board.n)
                    .filter(|&v| self.original.preserved[v] && !board.preserved[v])
                    .collect(),
            );
        };
        // Any successful deletion-only completion must remove an edge of
        // THIS current cycle. Branch on all its removable edges, deleting
        // every F endpoint. Recompute cycles after each choice: hitting only
        // the original fundamental-cycle basis would be unsound.
        let mut branches = BTreeSet::new();
        for edge in edges {
            if edge.iter().any(|&v| self.locked[v]) {
                continue;
            }
            let mut remove: Vec<_> = edge.into_iter().filter(|&v| board.preserved[v]).collect();
            remove.sort_unstable();
            if !remove.is_empty() && remove.len() <= budget {
                branches.insert(remove);
            }
        }
        for remove in branches {
            for &v in &remove {
                board.preserved[v] = false;
            }
            let result = self.visit(board, budget - remove.len());
            for &v in &remove {
                board.preserved[v] = true;
            }
            match result {
                Outcome::Exhausted => (),
                other => return other,
            }
        }
        Outcome::Exhausted
    }
}

/// Minimum ORIGINAL-F deletions for a fixed set of original-hole additions.
/// Negative conclusions are only within the stated deletion budget. A node
/// cutoff is never returned as an impossibility result.
pub fn repair(
    b: &Board,
    additions: &[usize],
    max_deletions: usize,
    node_limit: usize,
) -> Result<Repair, String> {
    if !(1..=15).contains(&b.n) {
        return Err("repair search is restricted to side 1..=15".into());
    }
    observe(b)?;
    if additions.is_empty() || max_deletions > 15 {
        return Err("require additions and a deletion budget at most 15".into());
    }
    let mut locked = vec![false; b.n * b.n];
    let mut board = b.clone();
    for &v in additions {
        if v >= locked.len() || b.preserved[v] || locked[v] {
            return Err("additions must be distinct original holes".into());
        }
        locked[v] = true;
        board.preserved[v] = true;
    }
    let mut search = Search {
        original: b,
        locked,
        nodes: 0,
        limit: node_limit,
        seen: HashSet::new(),
    };
    let mut report = Repair {
        status: RepairStatus::Cutoff,
        additions: additions.to_vec(),
        max_deletions,
        node_limit,
        nodes: 0,
        ruled_out_budgets_through: None,
        deleted: None,
        minimum_deletions: None,
        observation: None,
    };
    for budget in 0..=max_deletions {
        search.seen.clear();
        match search.visit(&mut board, budget) {
            Outcome::Found(deleted) => {
                for &v in &deleted {
                    board.preserved[v] = false;
                }
                report.observation = Some(observe(&board)?);
                report.minimum_deletions = Some(deleted.len());
                report.deleted = Some(deleted);
                report.status = RepairStatus::MinimumFound;
                break;
            }
            Outcome::Cutoff => break,
            Outcome::Exhausted => {
                report.ruled_out_budgets_through = Some(budget);
                if budget == max_deletions {
                    report.status = RepairStatus::NoRepairWithinBudget;
                }
            }
        }
    }
    report.nodes = search.nodes;
    Ok(report)
}

#[derive(Serialize)]
pub struct NeighborhoodScan {
    pub schema: &'static str,
    pub scope: &'static str,
    pub original: Observation,
    pub additions_per_query: usize,
    pub max_deletions: usize,
    pub node_limit_per_query: usize,
    pub query_limit: usize,
    pub total_combinations: usize,
    pub queries: usize,
    pub nodes: usize,
    pub cutoffs: usize,
    pub status: &'static str,
    pub improvement: Option<Repair>,
}

/// Scan all original-hole combinations of a fixed size (at most three),
/// until the first improving exchange or an explicit limit. No completion
/// is asserted when ANY query timed out or a combination was unexamined.
pub fn scan(
    b: &Board,
    additions: usize,
    node_limit: usize,
    query_limit: usize,
) -> Result<NeighborhoodScan, String> {
    if !(1..=15).contains(&b.n) {
        return Err("exchange scan is restricted to side 1..=15".into());
    }
    let original = observe(b)?;
    if !(1..=3).contains(&additions) {
        return Err("scan additions must be in 1..=3".into());
    }
    let holes: Vec<_> = (0..b.n * b.n).filter(|&v| !b.preserved[v]).collect();
    let total = if holes.len() < additions {
        0
    } else {
        (0..additions).fold(1usize, |n, j| n * (holes.len() - j) / (j + 1))
    };
    let mut report = NeighborhoodScan { schema: "grid-graphs.exchange-neighborhood.v1",
        scope: "this input board, fixed-size original-hole additions and at most additions-1 original-F deletions; not global optimality",
        original, additions_per_query: additions, max_deletions: additions-1,
        node_limit_per_query: node_limit, query_limit, total_combinations: total,
        queries: 0, nodes: 0, cutoffs: 0, status: "incomplete", improvement: None };
    let mut indices: Vec<_> = (0..additions).collect();
    while report.queries < total && report.queries < query_limit {
        let selected: Vec<_> = indices.iter().map(|&i| holes[i]).collect();
        let result = repair(b, &selected, additions - 1, node_limit)?;
        report.queries += 1;
        report.nodes += result.nodes;
        match result.status {
            RepairStatus::MinimumFound => {
                report.status = "improving_exchange_found";
                report.improvement = Some(result);
                return Ok(report);
            }
            RepairStatus::Cutoff => report.cutoffs += 1,
            RepairStatus::NoRepairWithinBudget => (),
        }
        if report.queries == total {
            break;
        }
        let j = (0..additions)
            .rev()
            .find(|&j| indices[j] < holes.len() - additions + j)
            .expect("another combination exists");
        indices[j] += 1;
        for k in j + 1..additions {
            indices[k] = indices[k - 1] + 1;
        }
    }
    if report.queries == total && report.cutoffs == 0 {
        report.status = "exhausted_neighborhood";
    }
    Ok(report)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn repairs_match_exhaustive_three_square_deletions_and_joint_additions() {
        for mask in 0u32..512 {
            let b = Board {
                n: 3,
                preserved: (0..9).map(|v| mask & (1 << v) != 0).collect(),
            };
            if observe(&b).is_err() {
                continue;
            }
            for additions_mask in 1u32..512 {
                if additions_mask & mask != 0 || additions_mask.count_ones() > 2 {
                    continue;
                }
                let adds: Vec<_> = (0..9).filter(|v| additions_mask & (1 << v) != 0).collect();
                let mut minimum = None;
                for deleted_mask in 0u32..512 {
                    if deleted_mask & !mask != 0 || deleted_mask.count_ones() > 2 {
                        continue;
                    }
                    let candidate = Board {
                        n: 3,
                        preserved: (0..9)
                            .map(|v| ((mask & !deleted_mask) | additions_mask) & (1 << v) != 0)
                            .collect(),
                    };
                    if observe(&candidate).is_ok() {
                        let d = deleted_mask.count_ones() as usize;
                        minimum = Some(minimum.map_or(d, |old: usize| old.min(d)));
                    }
                }
                let result = repair(&b, &adds, 2, 10000).unwrap();
                assert_ne!(result.status, RepairStatus::Cutoff);
                assert_eq!(
                    result.minimum_deletions, minimum,
                    "F={mask} add={additions_mask}"
                );
            }
        }
    }
    #[test]
    fn fixed_seventeen_diagnostics_and_search_guard() {
        let b = Board::parse(include_str!(
            "../analysis/residue_two_affine_17_witness.txt"
        ))
        .unwrap();
        let d = diagnose(&b).unwrap();
        assert_eq!(d.component_sizes, [288, 1]);
        assert_eq!(d.isolated_vertices, [36]);
        assert_eq!(
            d.promotion_cycle_rank_histogram,
            BTreeMap::from([(1, 3), (2, 22), (3, 154)])
        );
        for p in d.promotions {
            assert_eq!(p.blocking_paths.len(), p.cycle_rank);
            for path in p.blocking_paths {
                for e in path.removable_edges {
                    assert!(!e.edge.contains(&p.vertex));
                }
            }
        }
        assert!(repair(&b, &[36], 2, 100).is_err());
    }
    #[test]
    fn cutoff_is_not_a_negative_certificate_and_joint_additions_can_fail() {
        let b = Board::parse("UU\nUU").unwrap();
        let result = repair(&b, &[0, 3], 2, 0).unwrap();
        assert_eq!(result.status, RepairStatus::Cutoff);
        assert_eq!(result.ruled_out_budgets_through, None);
        assert_eq!(
            repair(&b, &[0, 3], 2, 10).unwrap().status,
            RepairStatus::NoRepairWithinBudget
        );
        assert_eq!(repair(&b, &[0], 0, 10).unwrap().minimum_deletions, Some(0));
        assert!(repair(&b, &[0, 0], 1, 10).is_err());
    }

    #[test]
    fn scan_distinguishes_complete_cutoff_and_early_success() {
        let empty = Board::parse("UU\nUU").unwrap();
        assert_eq!(
            scan(&empty, 1, 10, 4).unwrap().status,
            "improving_exchange_found"
        );
        let maximal = Board::parse("..\nUU").unwrap();
        let complete = scan(&maximal, 2, 100, 1).unwrap();
        assert_eq!(complete.total_combinations, 1);
        assert_eq!(complete.status, "exhausted_neighborhood");
        assert_eq!(scan(&maximal, 2, 0, 1).unwrap().status, "incomplete");
        assert_eq!(scan(&maximal, 2, 100, 0).unwrap().status, "incomplete");
        assert_eq!(
            scan(&maximal, 3, 100, 0).unwrap().status,
            "exhausted_neighborhood"
        );
    }

    #[test]
    fn cutting_every_displayed_basis_path_does_not_certify_repair() {
        let b = Board::parse(".UU\nUUU\n.U.").unwrap();
        let diagnostics = diagnose(&b).unwrap();
        let center = diagnostics
            .promotions
            .iter()
            .find(|p| p.vertex == 4)
            .unwrap();
        assert_eq!(center.cycle_rank, 3);
        assert_eq!(center.single_deletion_path_hits[&0], 3);
        let mut misleading = b.clone();
        misleading.preserved[0] = false;
        misleading.preserved[4] = true;
        assert!(observe(&misleading).is_err());
        assert_eq!(
            repair(&b, &[4], 3, 1000).unwrap().minimum_deletions,
            Some(3)
        );
    }
}
