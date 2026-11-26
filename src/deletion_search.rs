//! Exact fixed-deletion-size neighborhood search, with explicit work/time limits.
use crate::certificate_corpus::{observe, Board, Forest, Observation};
use serde::Serialize;
use std::collections::BTreeMap;
use std::time::{Duration, Instant};

#[derive(Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Status {
    ImprovingExchangeFound,
    ExhaustedNeighborhood,
    NodeLimit,
    TimeLimit,
}

#[derive(Serialize)]
pub struct Report {
    pub schema: &'static str,
    pub scope: &'static str,
    pub original: Observation,
    pub deletions_per_set: usize,
    pub additions_required: usize,
    pub total_deletion_sets: usize,
    pub deletion_sets_started: usize,
    pub deletion_sets_completed: usize,
    pub initially_legal_hole_histogram: BTreeMap<usize, usize>,
    pub nodes: u64,
    pub node_limit: u64,
    pub time_limit_ms: u64,
    pub elapsed_seconds: f64,
    pub status: Status,
    pub deleted: Option<Vec<usize>>,
    pub added: Option<Vec<usize>>,
    pub witness: Option<Observation>,
}

struct Budget {
    start: Instant,
    nodes: u64,
    limit: u64,
    duration: Duration,
}
impl Budget {
    fn step(&mut self) -> Result<(), Status> {
        if self.nodes >= self.limit {
            return Err(Status::NodeLimit);
        }
        if self.start.elapsed() >= self.duration {
            return Err(Status::TimeLimit);
        }
        self.nodes += 1;
        Ok(())
    }
}

fn augment(
    forest: &Forest,
    candidates: &[usize],
    start: usize,
    needed: usize,
    chosen: &mut Vec<usize>,
    budget: &mut Budget,
) -> Result<bool, Status> {
    if needed == 0 {
        return Ok(true);
    }
    if candidates.len() - start < needed {
        return Ok(false);
    }
    for i in start..=candidates.len() - needed {
        budget.step()?;
        if !forest.can_insert(candidates[i]) {
            continue;
        }
        let mut next = forest.clone();
        assert!(next.insert(candidates[i]));
        chosen.push(candidates[i]);
        if augment(&next, candidates, i + 1, needed - 1, chosen, budget)? {
            return Ok(true);
        }
        chosen.pop();
    }
    Ok(false)
}

/// All d-element subsets of original F; for each, all feasible (d+1)-element
/// subsets of original U. Invalid insertion prefixes can be discarded because
/// further insertions only add forced edges. No radius or motif restriction.
pub fn search(
    board: &Board,
    d: usize,
    node_limit: u64,
    time_limit_ms: u64,
) -> Result<Report, String> {
    if !(1..=15).contains(&board.n) {
        return Err("deletion-first search is restricted to side 1..=15".into());
    }
    if d > 4 {
        return Err("deletion size must be in 0..=4".into());
    }
    let original = observe(board)?;
    let selected: Vec<_> = (0..board.n * board.n)
        .filter(|&v| board.preserved[v])
        .collect();
    let holes: Vec<_> = (0..board.n * board.n)
        .filter(|&v| !board.preserved[v])
        .collect();
    let total = if selected.len() < d {
        0
    } else {
        (0..d).fold(1usize, |n, j| n * (selected.len() - j) / (j + 1))
    };
    let mut budget = Budget {
        start: Instant::now(),
        nodes: 0,
        limit: node_limit,
        duration: Duration::from_millis(time_limit_ms),
    };
    let mut report = Report { schema: "grid-graphs.deletion-first-neighborhood.v1",
        scope: "one input board; exactly d original-F deletions and d+1 original-hole additions; not global optimality",
        original, deletions_per_set: d, additions_required: d+1, total_deletion_sets: total,
        deletion_sets_started: 0, deletion_sets_completed: 0, nodes: 0, node_limit,
        initially_legal_hole_histogram: BTreeMap::new(),
        time_limit_ms, elapsed_seconds: 0.0, status: Status::ExhaustedNeighborhood,
        deleted: None, added: None, witness: None };
    let mut indices: Vec<_> = (0..d).collect();
    while report.deletion_sets_completed < total {
        if let Err(status) = budget.step() {
            report.status = status;
            break;
        }
        report.deletion_sets_started += 1;
        let removed: Vec<_> = indices.iter().map(|&i| selected[i]).collect();
        let mut reduced = board.clone();
        for &v in &removed {
            reduced.preserved[v] = false;
        }
        let forest = Forest::from_board(&reduced)?;
        let mut candidates = Vec::new();
        let mut stopped = None;
        // A hole illegal immediately after deletion cannot become legal after
        // adding other F vertices. This filter avoids most prefix branches.
        for &v in &holes {
            if let Err(status) = budget.step() {
                stopped = Some(status);
                break;
            }
            if forest.can_insert(v) {
                candidates.push(v);
            }
        }
        if let Some(status) = stopped {
            report.status = status;
            break;
        }
        let mut added = Vec::new();
        *report
            .initially_legal_hole_histogram
            .entry(candidates.len())
            .or_default() += 1;
        match augment(&forest, &candidates, 0, d + 1, &mut added, &mut budget) {
            Err(status) => {
                report.status = status;
                break;
            }
            Ok(true) => {
                for &v in &added {
                    reduced.preserved[v] = true;
                }
                let witness = observe(&reduced)?;
                if witness.features["f"] != report.original.features["f"] + 1 {
                    return Err("exchange score mismatch".into());
                }
                report.status = Status::ImprovingExchangeFound;
                report.deleted = Some(removed);
                report.added = Some(added);
                report.witness = Some(witness);
                break;
            }
            Ok(false) => report.deletion_sets_completed += 1,
        }
        if report.deletion_sets_completed == total {
            break;
        }
        let j = (0..d)
            .rev()
            .find(|&j| indices[j] < selected.len() - d + j)
            .expect("another deletion combination exists");
        indices[j] += 1;
        for k in j + 1..d {
            indices[k] = indices[k - 1] + 1;
        }
    }
    report.nodes = budget.nodes;
    report.elapsed_seconds = budget.start.elapsed().as_secs_f64();
    Ok(report)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn complete_three_square_comparison_through_four_deletions() {
        for mask in 0u32..512 {
            let b = Board {
                n: 3,
                preserved: (0..9).map(|v| mask & (1 << v) != 0).collect(),
            };
            if observe(&b).is_err() {
                continue;
            }
            for d in 0..=4 {
                let expected = (0u32..512).any(|final_mask| {
                    (mask & !final_mask).count_ones() == d as u32
                        && (final_mask & !mask).count_ones() == d as u32 + 1
                        && observe(&Board {
                            n: 3,
                            preserved: (0..9).map(|v| final_mask & (1 << v) != 0).collect(),
                        })
                        .is_ok()
                });
                let result = search(&b, d, 1_000_000, 60_000).unwrap();
                assert!(matches!(
                    result.status,
                    Status::ImprovingExchangeFound | Status::ExhaustedNeighborhood
                ));
                assert_eq!(result.witness.is_some(), expected, "mask={mask} d={d}");
                if !expected {
                    assert_eq!(result.deletion_sets_completed, result.total_deletion_sets);
                }
            }
        }
    }
    #[test]
    fn limits_and_scope_are_explicit() {
        let b = Board::parse("..\nUU").unwrap();
        assert_eq!(search(&b, 1, 0, 1000).unwrap().status, Status::NodeLimit);
        assert_eq!(search(&b, 1, 100, 0).unwrap().status, Status::TimeLimit);
        assert_eq!(
            search(&b, 3, 0, 0).unwrap().status,
            Status::ExhaustedNeighborhood
        );
        assert!(search(&b, 5, 100, 1000).is_err());
        let big = Board {
            n: 17,
            preserved: vec![false; 289],
        };
        assert!(search(&big, 3, 100, 1000).is_err());
    }

    #[test]
    fn four_for_five_matches_literal_four_square_final_boards() {
        let mut successes = 0;
        let mut failures = 0;
        for mask in [0x000fu32, 0x100f, 0x900f, 0xd00f, 0xf00f] {
            let b = Board {
                n: 4,
                preserved: (0..16).map(|v| mask & (1 << v) != 0).collect(),
            };
            observe(&b).unwrap();
            let expected = (0u32..1 << 16).any(|final_mask| {
                (mask & !final_mask).count_ones() == 4
                    && (final_mask & !mask).count_ones() == 5
                    && observe(&Board {
                        n: 4,
                        preserved: (0..16).map(|v| final_mask & (1 << v) != 0).collect(),
                    })
                    .is_ok()
            });
            let result = search(&b, 4, 1_000_000, 60_000).unwrap();
            assert_eq!(result.witness.is_some(), expected, "mask={mask:x}");
            if expected {
                successes += 1;
                assert_eq!(result.status, Status::ImprovingExchangeFound);
                assert_eq!(result.deleted.as_ref().unwrap().len(), 4);
                assert_eq!(result.added.as_ref().unwrap().len(), 5);
                assert_eq!(
                    result.witness.unwrap().features["f"],
                    mask.count_ones() as i64 + 1
                );
            } else {
                failures += 1;
                assert_eq!(result.status, Status::ExhaustedNeighborhood);
                assert_eq!(result.deletion_sets_completed, result.total_deletion_sets);
            }
        }
        assert!(successes > 0 && failures > 0);
    }

    #[test]
    fn four_for_five_prefix_cutoff_cannot_be_reported_as_exhausted() {
        let b = Board::parse("....\nUUUU\nUUUU\nUUUU").unwrap();
        // One deletion evaluation, twelve hole tests, then one prefix test.
        let result = search(&b, 4, 14, 60_000).unwrap();
        assert_eq!(result.status, Status::NodeLimit);
        assert_eq!(result.nodes, 14);
        assert_eq!(result.deletion_sets_started, 1);
        assert_eq!(result.deletion_sets_completed, 0);
        assert!(result.witness.is_none());
        assert_eq!(search(&b, 4, 1000, 0).unwrap().status, Status::TimeLimit);
    }
}
