//! Exact finite fillings with actual exterior components; no virtual bank edges.
use crate::certificate_corpus::{observe, Board};
use serde::Serialize;
use std::collections::BTreeMap;

#[derive(Clone)]
struct Dsu(Vec<usize>);
impl Dsu {
    fn new(n: usize) -> Self {
        Self((0..n).collect())
    }
    fn root(&mut self, x: usize) -> usize {
        if self.0[x] != x {
            self.0[x] = self.root(self.0[x]);
        }
        self.0[x]
    }
    fn join(&mut self, a: usize, b: usize) -> bool {
        let (a, b) = (self.root(a), self.root(b));
        if a == b {
            return false;
        }
        self.0[b] = a;
        true
    }
}

fn edges(n: usize) -> Vec<(usize, usize)> {
    let mut out = Vec::new();
    for v in 0..n * n {
        if v % n + 1 < n {
            out.push((v, v + 1));
        }
        if v / n + 1 < n {
            out.push((v, v + n));
        }
    }
    out
}

/// The port order is physical row-major order. Root labels are canonical.
#[derive(Clone, Debug, Serialize)]
pub struct Port {
    pub vertex: usize,
    pub preserved: bool,
    pub root: usize,
}

pub struct Interface {
    baseline: Board,
    inside: Vec<bool>,
    optional: Vec<usize>,
    local_edges: Vec<(usize, usize)>,
    pub ports: Vec<Port>,
    pub outside_closed: usize,
    pub identifications: usize,
}

impl Interface {
    /// Baseline F inside the region are mandatory. Outside is fixed.
    pub fn new(baseline: Board, region: &[usize]) -> Result<Self, String> {
        if baseline.n == 0 || baseline.n > 15 {
            return Err("interface experiments require side 1..=15".into());
        }
        observe(&baseline)?;
        let size = baseline.n * baseline.n;
        let mut inside = vec![false; size];
        for &v in region {
            if v >= size || inside[v] {
                return Err("invalid or duplicate region vertex".into());
            }
            inside[v] = true;
        }
        let optional: Vec<_> = region
            .iter()
            .copied()
            .filter(|&v| !baseline.preserved[v])
            .collect();
        if optional.len() > 20 {
            return Err("complete enumeration capped at 20 optional vertices".into());
        }
        let mut exterior = Dsu::new(size);
        let mut port = vec![false; size];
        let mut local_edges = Vec::new();
        for (v, w) in edges(baseline.n) {
            if inside[v] || inside[w] {
                local_edges.push((v, w));
                if inside[v] != inside[w] {
                    port[if inside[v] { w } else { v }] = true;
                }
            } else if baseline.preserved[v] || baseline.preserved[w] {
                assert!(exterior.join(v, w));
            }
        }
        let mut roots = BTreeMap::new();
        let mut ports = Vec::new();
        for v in 0..size {
            if port[v] {
                let next = roots.len();
                let root = *roots.entry(exterior.root(v)).or_insert(next);
                ports.push(Port {
                    vertex: v,
                    preserved: baseline.preserved[v],
                    root,
                });
            }
        }
        let identifications = ports.len() - roots.len();
        let mut closed = std::collections::BTreeSet::new();
        for (v, &is_inside) in inside.iter().enumerate() {
            if !is_inside {
                let r = exterior.root(v);
                if !roots.contains_key(&r) {
                    closed.insert(r);
                }
            }
        }
        Ok(Self {
            baseline,
            inside,
            optional,
            local_edges,
            ports,
            outside_closed: closed.len(),
            identifications,
        })
    }

    pub(crate) fn board(&self, mask: u64) -> Board {
        let mut board = self.baseline.clone();
        for (i, &v) in self.optional.iter().enumerate() {
            board.preserved[v] = mask & (1 << i) != 0;
        }
        board
    }

    pub(crate) fn cycle_rank(&self, board: &Board, split: bool) -> usize {
        let mut dsu = Dsu::new(board.n * board.n);
        if !split {
            let mut first = BTreeMap::new();
            for p in &self.ports {
                if let Some(&v) = first.get(&p.root) {
                    assert!(dsu.join(v, p.vertex));
                } else {
                    first.insert(p.root, p.vertex);
                }
            }
        }
        let mut rank = 0;
        for &(v, w) in &self.local_edges {
            if (board.preserved[v] || board.preserved[w]) && !dsu.join(v, w) {
                rank += 1;
            }
        }
        rank
    }

    pub fn enumerate(&self, literal_audit: bool) -> FillingResult {
        self.enumerate_profile(literal_audit).0
    }

    /// Exact best optional score at each actual rank among relaxed forests.
    pub fn enumerate_profile(&self, literal_audit: bool) -> (FillingResult, Vec<RankLevel>) {
        let mut profile: BTreeMap<usize, RankLevel> = BTreeMap::new();
        let mut result = FillingResult {
            tested: 0,
            feasible: 0,
            relaxed_feasible: 0,
            optimum: 0,
            relaxed_optimum: 0,
            identifications: self.identifications,
            best_rows: Vec::new(),
            relaxed_best_rows: Vec::new(),
        };
        let mut penalized_optimum = i64::MIN;
        for mask in 0..1u64 << self.optional.len() {
            let board = self.board(mask);
            let rank = self.cycle_rank(&board, false);
            let legal = rank == 0;
            let relaxed = self.cycle_rank(&board, true) == 0;
            if literal_audit {
                assert_eq!(legal, observe(&board).is_ok());
            }
            assert!(!legal || relaxed);
            result.tested += 1;
            let gain = mask.count_ones() as usize;
            if legal {
                result.feasible += 1;
                check_gluing(&board, &self.inside);
                if result.best_rows.is_empty() || gain > result.optimum {
                    result.optimum = gain;
                    result.best_rows = board.rows();
                }
            }
            if relaxed {
                let level = profile.entry(rank).or_insert(RankLevel {
                    rank,
                    best_optional: gain,
                    mask,
                    count: 0,
                });
                level.count += 1;
                if gain > level.best_optional {
                    level.best_optional = gain;
                    level.mask = mask;
                }
                penalized_optimum = penalized_optimum.max(gain as i64 - 2 * rank as i64);
                result.relaxed_feasible += 1;
                if result.relaxed_best_rows.is_empty() || gain > result.relaxed_optimum {
                    result.relaxed_optimum = gain;
                    result.relaxed_best_rows = board.rows();
                }
            }
        }
        assert!(result.relaxed_optimum >= result.optimum);
        assert!(result.relaxed_optimum - result.optimum <= 2 * self.identifications);
        assert_eq!(penalized_optimum, result.optimum as i64);
        (result, profile.into_values().collect())
    }
}

#[derive(Debug, Serialize)]
pub struct RankLevel {
    pub rank: usize,
    pub best_optional: usize,
    pub mask: u64,
    pub count: u64,
}

/// Direct induced-side ledger, counting even sealed isolated vertices.
fn side_ledger(board: &Board, side: &[bool], take: bool) -> (i64, i64, i64) {
    let mut h = Dsu::new(side.len());
    let mut f = Dsu::new(side.len());
    let mut c = side.iter().filter(|&&s| s == take).count() as i64;
    let mut r = (0..side.len())
        .filter(|&v| side[v] == take && board.preserved[v])
        .count() as i64;
    let mut b = 4
        * (0..side.len())
            .filter(|&v| side[v] == take && !board.preserved[v])
            .count() as i64;
    for (v, w) in edges(board.n) {
        if side[v] != take || side[w] != take {
            continue;
        }
        b -= i64::from(!board.preserved[v]) + i64::from(!board.preserved[w]);
        if board.preserved[v] || board.preserved[w] {
            assert!(h.join(v, w));
            c -= 1;
        }
        if board.preserved[v] && board.preserved[w] {
            assert!(f.join(v, w));
            r -= 1;
        }
    }
    (r, b, c)
}

fn check_gluing(board: &Board, inside: &[bool]) {
    let (ri, bi, ci) = side_ledger(board, inside, true);
    let (ro, bo, co) = side_ledger(board, inside, false);
    let (r, b, c) = side_ledger(board, &vec![true; inside.len()], true);
    let (mut cut, mut forced, mut ff) = (0, 0, 0);
    for (v, w) in edges(board.n) {
        if inside[v] != inside[w] {
            cut += 1;
            forced += i64::from(board.preserved[v] || board.preserved[w]);
            ff += i64::from(board.preserved[v] && board.preserved[w]);
        }
    }
    assert_eq!(ci + co, c + forced);
    assert_eq!(ri + ro, r + ff);
    assert_eq!(bi + bo, b + 2 * cut - forced - ff);
    assert_eq!(ri + bi + ci + ro + bo + co, r + b + c + 2 * cut);
}

#[derive(Debug, Serialize)]
pub struct FillingResult {
    pub tested: u64,
    pub feasible: u64,
    pub relaxed_feasible: u64,
    pub optimum: usize,
    pub relaxed_optimum: usize,
    pub identifications: usize,
    pub best_rows: Vec<String>,
    /// A relaxed filling can be cyclic with the actual exterior!
    pub relaxed_best_rows: Vec<String>,
}

#[derive(Serialize)]
pub struct Case {
    pub name: String,
    pub baseline: Vec<String>,
    pub region: Vec<usize>,
    pub ports: Vec<Port>,
    pub outside_closed: usize,
    pub result: FillingResult,
}

fn case(name: String, board: Board, region: &[usize]) -> Option<Case> {
    let interface = Interface::new(board, region).ok()?;
    let result = interface.enumerate(true);
    Some(Case {
        name,
        baseline: interface.baseline.rows(),
        region: region.to_vec(),
        ports: interface.ports,
        outside_closed: interface.outside_closed,
        result,
    })
}

/// All 1024 exterior labelings; infeasible baselines imply no feasible filling.
pub fn four_square() -> Vec<Case> {
    let region = vec![5, 6, 7, 9, 10, 11];
    let outside: Vec<_> = (0..16).filter(|v| !region.contains(v)).collect();
    let mut cases = Vec::new();
    for mask in 0..1u64 << outside.len() {
        let mut board = Board {
            n: 4,
            preserved: vec![false; 16],
        };
        for (i, &v) in outside.iter().enumerate() {
            board.preserved[v] = mask & (1 << i) != 0;
        }
        if let Some(c) = case(format!("exterior_{mask}"), board, &region) {
            cases.push(c);
        }
    }
    cases
}

/// Nine one-step seam skeletons, and each possible single outside promotion.
pub fn moving_seams() -> Vec<Case> {
    let region: Vec<_> = (2..=4)
        .flat_map(|y| (2..=5).map(move |x| y * 9 + x))
        .collect();
    let mut cases = Vec::new();
    for a0 in 2..=4 {
        for a1 in 2..=4 {
            let mut base = Board {
                n: 9,
                preserved: vec![false; 81],
            };
            for (j, a) in [a0, a1].into_iter().enumerate() {
                for x in 1..=a {
                    base.preserved[(1 + 3 * j) * 9 + x] = true;
                }
                for x in a + 2..=7 {
                    base.preserved[(2 + 3 * j) * 9 + x] = true;
                }
            }
            for addition in std::iter::once(None).chain(
                (0..81)
                    .filter(|v| !region.contains(v) && !base.preserved[*v])
                    .map(Some),
            ) {
                let mut board = base.clone();
                if let Some(v) = addition {
                    board.preserved[v] = true;
                }
                if let Some(c) = case(
                    format!("seam_{a0}_{a1}_outside_{addition:?}"),
                    board,
                    &region,
                ) {
                    cases.push(c);
                }
            }
        }
    }
    cases
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn single_actual_exterior_identification_has_sharp_price() {
        let mut board = Board {
            n: 3,
            preserved: vec![false; 9],
        };
        board.preserved[0] = true;
        let interface = Interface::new(board, &[4]).unwrap();
        let result = interface.enumerate(true);
        assert_eq!(result.identifications, 1);
        assert_eq!((result.optimum, result.relaxed_optimum), (0, 1));
    }

    #[test]
    fn ff_cycle_refutes_unit_rank_price_and_makes_factor_two_sharp() {
        let board = Board::parse(".U..\nUUUU\n.UUU\nUU.U").unwrap();
        let mut interface = Interface::new(board, &[5, 6, 7, 9, 10, 11]).unwrap();
        let actual = interface.enumerate(true);
        assert_eq!(actual.optimum, 0);
        let candidate = Board::parse(".U..\nUU..\n.UUU\nUU.U").unwrap();
        assert_eq!(interface.cycle_rank(&candidate, false), 1);
        // Split exactly one port off its actual exterior root. This is an
        // abstract refinement, not a second full-board exterior realization.
        interface
            .ports
            .iter_mut()
            .find(|p| p.vertex == 3)
            .unwrap()
            .root = 2;
        assert_eq!(interface.cycle_rank(&interface.baseline, false), 0);
        let finer_optimum = (0..1u64 << interface.optional.len())
            .filter(|&mask| interface.cycle_rank(&interface.board(mask), false) == 0)
            .map(|mask| mask.count_ones())
            .max()
            .unwrap();
        assert_eq!(finer_optimum, 2);
    }

    #[test]
    fn exhaustive_four_square_exterior_and_full_graph_agree() {
        let cases = four_square();
        assert!(!cases.is_empty());
        assert!(cases
            .iter()
            .any(|c| c.result.optimum < c.result.relaxed_optimum));
        // All omitted baselines have a literal cycle, which persists under additions.
        let region = [5, 6, 7, 9, 10, 11];
        for mask in 0..1u64 << 16 {
            let board = Board {
                n: 4,
                preserved: (0..16).map(|i| mask & (1 << i) != 0).collect(),
            };
            let mut baseline = board.clone();
            for &v in &region {
                baseline.preserved[v] = false;
            }
            if observe(&baseline).is_err() {
                assert!(observe(&board).is_err());
            }
        }
    }

    #[test]
    fn actual_partial_seams_obey_rank_price_and_gluing() {
        let cases = moving_seams();
        assert!(!cases.is_empty());
        assert!(cases
            .iter()
            .any(|c| c.ports.iter().map(|p| p.root).max().unwrap_or(0) > 1));
    }
}
