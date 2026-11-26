//! Exact omission/reordering within a recorded move vocabulary, not a global
//! shortest-path search. The final improving exchange is held fixed.
use crate::certificate_corpus::{observe, Board, Observation};
use crate::neutral_search::{replay, Move, Report, TraceStep};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::time::Instant;

#[derive(Serialize, Deserialize)]
pub struct Simplification {
    pub schema: String,
    pub scope: String,
    pub ordered_only: bool,
    pub mixed: bool,
    pub source_neutral_moves: usize,
    pub retained_source_indices: Vec<usize>, // One-based neutral-move IDs.
    pub minimum_proved: bool,
    pub status: String,
    pub states_discovered: usize,
    pub states_examined: usize,
    pub move_tests: usize,
    pub gain_tests: usize,
    pub state_limit: usize,
    pub time_limit_ms: u64,
    pub elapsed_seconds: f64,
    pub original: Observation,
    pub trace: Vec<TraceStep>,
    pub endpoint: Observation,
}

fn apply(b: &Board, m: &Move, score: i64) -> Option<Board> {
    let d: BTreeSet<_> = m.deleted.iter().copied().collect();
    let a: BTreeSet<_> = m.added.iter().copied().collect();
    if d.len() != m.deleted.len()
        || a.len() != m.added.len()
        || d.iter().any(|&v| v >= b.preserved.len() || !b.preserved[v])
        || a.iter().any(|&v| v >= b.preserved.len() || b.preserved[v])
    {
        return None;
    }
    let mut next = b.clone();
    for v in d {
        next.preserved[v] = false;
    }
    for v in a {
        next.preserved[v] = true;
    }
    let o = observe(&next).ok()?;
    (o.features["f"] == score).then_some(next)
}

struct State {
    board: Board,
    parent: Option<(usize, usize)>,
}

pub fn simplify(
    source: &Report,
    ordered_only: bool,
    state_limit: usize,
    time_limit_ms: u64,
) -> Result<Simplification, String> {
    if source.status != "escape_found" {
        return Err("need a recorded escape".into());
    }
    let original = Board::parse(&source.original.rows.join("\n"))?;
    replay(&original, &source.trace, true)?;
    let count = source.trace.len() - 1;
    if count > 20 || state_limit == 0 {
        return Err("require at most 20 neutral moves and a positive state limit".into());
    }
    let moves: Vec<_> = source.trace[..count]
        .iter()
        .map(|s| s.exchange.clone())
        .collect();
    let gain = source.trace[count].exchange.clone();
    let initial = observe(&original)?;
    let score = initial.features["f"];
    let started = Instant::now();
    let mut states = BTreeMap::from([(
        0usize,
        State {
            board: original.clone(),
            parent: None,
        },
    )]);
    let mut queue = VecDeque::from([0usize]);
    let (mut examined, mut move_tests, mut gain_tests) = (0, 0, 0);
    let mut chosen = None;
    let mut status = "minimum_found";
    'search: while let Some(mask) = queue.pop_front() {
        if started.elapsed().as_millis() >= u128::from(time_limit_ms) {
            status = "time_limit";
            break;
        }
        examined += 1;
        gain_tests += 1;
        let board = states[&mask].board.clone();
        if apply(&board, &gain, score + 1).is_some() {
            chosen = Some(mask);
            break;
        }
        for (i, m) in moves.iter().enumerate() {
            if mask & (1 << i) != 0 || (ordered_only && mask >> (i + 1) != 0) {
                continue;
            }
            let next_mask = mask | (1 << i);
            if states.contains_key(&next_mask) {
                continue;
            }
            if started.elapsed().as_millis() >= u128::from(time_limit_ms) {
                status = "time_limit";
                break 'search;
            }
            move_tests += 1;
            if let Some(next) = apply(&board, m, score) {
                if states.len() >= state_limit {
                    status = "state_limit";
                    break 'search;
                }
                states.insert(
                    next_mask,
                    State {
                        board: next,
                        parent: Some((mask, i)),
                    },
                );
                queue.push_back(next_mask);
            }
        }
    }
    if chosen.is_none() && status == "minimum_found" {
        return Err("complete simplification lost the known original route".into());
    }
    let minimum_proved = chosen.is_some();
    let mut indices = Vec::new();
    if let Some(mut mask) = chosen {
        while let Some((parent, i)) = states[&mask].parent {
            indices.push(i);
            mask = parent;
        }
        indices.reverse();
    } else {
        indices.extend(0..count);
    }
    let mut b = original.clone();
    let mut trace = Vec::new();
    for (index, m) in indices
        .iter()
        .map(|&i| &moves[i])
        .chain(std::iter::once(&gain))
        .enumerate()
    {
        b = apply(&b, m, score + i64::from(index == indices.len()))
            .ok_or("invalid reconstructed simplification")?;
        trace.push(TraceStep {
            exchange: m.clone(),
            rows: b.rows(),
            f: score + i64::from(index == indices.len()),
            missing_original_f: original
                .preserved
                .iter()
                .zip(&b.preserved)
                .filter(|(a, c)| **a && !**c)
                .count(),
        });
    }
    let endpoint = replay(&original, &trace, true)?;
    Ok(Simplification {schema:"grid-graphs.neutral-simplification.v1".into(),
        scope:"minimum number of retained recorded neutral moves, each usable at most once, before the unchanged final gain; not a global shortest route".into(),
        ordered_only,mixed:source.config.mixed,source_neutral_moves:count,
        retained_source_indices:indices.into_iter().map(|i|i+1).collect(),minimum_proved,status:status.into(),
        states_discovered:states.len(),states_examined:examined,move_tests,gain_tests,state_limit,time_limit_ms,
        elapsed_seconds:started.elapsed().as_secs_f64(),original:initial,trace,endpoint})
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::neutral_search::{Config, Stats};
    fn example() -> Report {
        let b = Board::parse(".UU\nUUU\nUUU").unwrap();
        let moves = [
            Move {
                deleted: vec![0],
                added: vec![1],
            },
            Move {
                deleted: vec![1],
                added: vec![0],
            },
            Move {
                deleted: vec![],
                added: vec![2],
            },
        ];
        let mut current = b.clone();
        let mut trace = Vec::new();
        for (i, m) in moves.into_iter().enumerate() {
            current = apply(&current, &m, if i == 2 { 2 } else { 1 }).unwrap();
            trace.push(TraceStep {
                exchange: m,
                rows: current.rows(),
                f: if i == 2 { 2 } else { 1 },
                missing_original_f: usize::from(!current.preserved[0]),
            });
        }
        Report {
            schema: "grid-graphs.neutral-plateau.v1".into(),
            scope: "test".into(),
            config: Config::default(),
            original: observe(&b).unwrap(),
            status: "escape_found".into(),
            original_excluded_deletion_radius: None,
            original_bound_source: None,
            stats: Stats::default(),
            layers: vec![],
            trace_kind: "escape".into(),
            trace,
            endpoint: observe(&current).unwrap(),
        }
    }
    #[test]
    fn omission_and_limits_keep_valid_witnesses() {
        let source = example();
        for ordered in [true, false] {
            let s = simplify(&source, ordered, 100, 1000).unwrap();
            assert!(s.minimum_proved);
            assert_eq!(s.retained_source_indices, Vec::<usize>::new());
            assert_eq!(s.trace.len(), 1);
        }
        let s = simplify(&source, false, 100, 0).unwrap();
        assert!(!s.minimum_proved);
        assert_eq!(s.status, "time_limit");
        assert_eq!(s.trace.len(), source.trace.len());
    }
    #[test]
    fn archived_route_is_replayed_for_both_order_rules() {
        let source: Report =
            serde_json::from_str(include_str!("../data/neutral_escape_14.json")).unwrap();
        let a = simplify(&source, true, 4096, 10_000).unwrap();
        let b = simplify(&source, false, 4096, 10_000).unwrap();
        assert!(a.minimum_proved && b.minimum_proved);
        assert!(b.trace.len() <= a.trace.len());
        assert_eq!(b.endpoint.features["f"], 77);
        let capped = simplify(&source, false, 1, 10_000).unwrap();
        assert_eq!(capped.status, "state_limit");
        assert!(!capped.minimum_proved);
    }

    #[test]
    fn subset_bfs_matches_unmemoized_permutation_search() {
        let mut source = example();
        let b = Board::parse(".UU\nUUU\nUUU").unwrap();
        let neutrals = vec![
            Move {
                deleted: vec![0],
                added: vec![2],
            },
            Move {
                deleted: vec![2],
                added: vec![1],
            },
            Move {
                deleted: vec![1],
                added: vec![0],
            },
            Move {
                deleted: vec![0],
                added: vec![1],
            },
        ];
        let gain = Move {
            deleted: vec![],
            added: vec![4],
        };
        let mut current = b.clone();
        source.trace.clear();
        for (i, m) in neutrals.iter().chain(std::iter::once(&gain)).enumerate() {
            current = apply(&current, m, if i == 4 { 2 } else { 1 }).unwrap();
            source.trace.push(TraceStep {
                exchange: m.clone(),
                rows: current.rows(),
                f: if i == 4 { 2 } else { 1 },
                missing_original_f: usize::from(!current.preserved[0]),
            });
        }
        source.endpoint = observe(&current).unwrap();
        fn brute(
            b: &Board,
            moves: &[Move],
            gain: &Move,
            used: u32,
            ordered: bool,
        ) -> Option<usize> {
            if apply(b, gain, 2).is_some() {
                return Some(0);
            }
            moves
                .iter()
                .enumerate()
                .filter(|(i, _)| used & (1 << i) == 0 && (!ordered || used >> (i + 1) == 0))
                .filter_map(|(i, m)| {
                    apply(b, m, 1)
                        .and_then(|next| brute(&next, moves, gain, used | (1 << i), ordered))
                        .map(|n| n + 1)
                })
                .min()
        }
        for ordered in [true, false] {
            let expected = brute(&b, &neutrals, &gain, 0, ordered).unwrap();
            assert!(expected > 0);
            let result = simplify(&source, ordered, 1000, 1000).unwrap();
            assert!(result.minimum_proved);
            assert_eq!(result.retained_source_indices.len(), expected);
        }
    }
}
