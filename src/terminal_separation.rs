//! Exact maximum-score fillings subject to an actual terminal separation.
use crate::boundary_conditioned::Interface;
use crate::certificate_corpus::{observe, Board};
use serde::Serialize;
use std::collections::VecDeque;

/// Literal BFS, independent of the contracted-interface union-find.
fn components(board: &Board) -> (Vec<usize>, usize, bool) {
    let mut labels = vec![usize::MAX; board.n * board.n];
    let mut count = 0;
    let mut forest = true;
    for start in 0..labels.len() {
        if labels[start] != usize::MAX {
            continue;
        }
        labels[start] = count;
        let mut queue = VecDeque::from([start]);
        let (mut vertices, mut degree) = (0, 0);
        while let Some(v) = queue.pop_front() {
            vertices += 1;
            for w in board.neighbors(v) {
                if !(board.preserved[v] || board.preserved[w]) {
                    continue;
                }
                degree += 1;
                if labels[w] == usize::MAX {
                    labels[w] = count;
                    queue.push_back(w);
                }
            }
        }
        forest &= degree == 2 * (vertices - 1);
        count += 1;
    }
    (labels, count, forest)
}

#[derive(Clone, Copy, Debug, Serialize)]
pub struct Terminal {
    pub v: usize,
    pub w: usize,
}

pub fn blocked_terminals(board: &Board) -> Vec<Terminal> {
    let (labels, _, forest) = components(board);
    assert!(forest);
    (0..board.n * board.n)
        .filter_map(|v| {
            if board.preserved[v] {
                return None;
            }
            let holes: Vec<_> = board
                .neighbors(v)
                .filter(|&w| !board.preserved[w])
                .collect();
            (holes.len() == 1 && labels[v] == labels[holes[0]]).then(|| Terminal { v, w: holes[0] })
        })
        .collect()
}

#[derive(Debug, Serialize)]
pub struct Separation {
    pub terminal: Terminal,
    pub clearing_separates: bool,
    pub best_separated: Option<usize>,
    pub best_mask: Option<u64>,
    pub neutral_mask: Option<u64>,
    pub neutral_deleted: Vec<usize>,
    pub neutral_added: Vec<usize>,
    pub neutral_components: Option<usize>,
    pub promoted_rows: Option<Vec<String>>,
}

#[derive(Debug, Serialize)]
pub struct RegionResult {
    pub region: Vec<usize>,
    pub original_score: usize,
    pub original_components: usize,
    pub fillings_tested: u64,
    pub feasible_fillings: u64,
    pub terminals: Vec<Separation>,
}

pub fn scan(
    board: &Board,
    region: &[usize],
    terminals: &[Terminal],
) -> Result<RegionResult, String> {
    observe(board)?;
    let mut baseline = board.clone();
    for &v in region {
        if v >= baseline.preserved.len() {
            return Err("invalid core vertex".into());
        }
        baseline.preserved[v] = false;
    }
    let interface = Interface::new(baseline.clone(), region)?;
    let (base_labels, _, base_forest) = components(&baseline);
    assert!(base_forest);
    let original_score = region.iter().filter(|&&v| board.preserved[v]).count();
    let mut result = RegionResult {
        region: region.to_vec(),
        original_score,
        original_components: components(board).1,
        fillings_tested: 0,
        feasible_fillings: 0,
        terminals: terminals
            .iter()
            .filter(|t| {
                !region.contains(&t.v) && board.neighbors(t.v).all(|w| !region.contains(&w))
            })
            .map(|&terminal| Separation {
                terminal,
                clearing_separates: base_labels[terminal.v] != base_labels[terminal.w],
                best_separated: None,
                best_mask: None,
                neutral_mask: None,
                neutral_deleted: Vec::new(),
                neutral_added: Vec::new(),
                neutral_components: None,
                promoted_rows: None,
            })
            .collect(),
    };
    if !result.terminals.iter().any(|t| t.clearing_separates) {
        return Ok(result);
    }
    for mask in 0..1u64 << region.len() {
        let candidate = interface.board(mask);
        let (labels, count, forest) = components(&candidate);
        assert_eq!(forest, interface.cycle_rank(&candidate, false) == 0);
        result.fillings_tested += 1;
        if !forest {
            continue;
        }
        result.feasible_fillings += 1;
        let score = mask.count_ones() as usize;
        for t in &mut result.terminals {
            if labels[t.terminal.v] == labels[t.terminal.w] {
                continue;
            }
            assert!(t.clearing_separates);
            if t.best_separated.is_none_or(|old| score > old) {
                t.best_separated = Some(score);
                t.best_mask = Some(mask);
            }
            if score == original_score && t.neutral_mask.is_none() {
                t.neutral_mask = Some(mask);
                t.neutral_components = Some(count);
                t.neutral_deleted = region
                    .iter()
                    .copied()
                    .filter(|&v| board.preserved[v] && !candidate.preserved[v])
                    .collect();
                t.neutral_added = region
                    .iter()
                    .copied()
                    .filter(|&v| !board.preserved[v] && candidate.preserved[v])
                    .collect();
                let mut promoted = candidate.clone();
                promoted.preserved[t.terminal.v] = true;
                let observation = observe(&promoted)?;
                assert_eq!(
                    observation.features["f"],
                    board.preserved.iter().filter(|&&f| f).count() as i64 + 1
                );
                assert_eq!(observation.features["c"], count as i64 - 1);
                t.promoted_rows = Some(promoted.rows());
            }
        }
    }
    for t in &result.terminals {
        assert_eq!(t.clearing_separates, t.best_separated.is_some());
        if let Some(best) = t.best_separated {
            // A removable edge on the original unique terminal path has
            // at most two F endpoints. Deleting both separates the terminals.
            assert!(best >= original_score.saturating_sub(2));
        }
        assert_eq!(
            t.neutral_mask.is_some(),
            t.best_separated.is_some_and(|s| s >= original_score)
        );
    }
    Ok(result)
}

pub fn rectangles(n: usize) -> Vec<Vec<usize>> {
    let mut regions = Vec::new();
    for (w, h) in [(3, 4), (4, 3)] {
        for y in 1..n.saturating_sub(h) {
            for x in 1..n.saturating_sub(w) {
                regions.push(
                    (y..y + h)
                        .flat_map(|yy| (x..x + w).map(move |xx| yy * n + xx))
                        .collect(),
                );
            }
        }
    }
    regions
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn complete_three_square_separation_matches_promotions() {
        for mask in 0..512u64 {
            let board = Board {
                n: 3,
                preserved: (0..9).map(|v| mask & (1 << v) != 0).collect(),
            };
            if observe(&board).is_err() {
                continue;
            }
            let terminals = blocked_terminals(&board);
            for region in [vec![4], vec![3, 4, 5], vec![0, 1, 2]] {
                let result = scan(&board, &region, &terminals).unwrap();
                for t in result.terminals {
                    let mut best = None;
                    for fill in 0..1u64 << region.len() {
                        let mut candidate = board.clone();
                        for (i, &v) in region.iter().enumerate() {
                            candidate.preserved[v] = fill & (1 << i) != 0;
                        }
                        // Full promotion is an independent oracle for separation.
                        candidate.preserved[t.terminal.v] = true;
                        if observe(&candidate).is_ok() {
                            best = Some(best.unwrap_or(0).max(fill.count_ones() as usize));
                        }
                    }
                    assert_eq!(t.best_separated, best);
                }
            }
        }
    }
}
