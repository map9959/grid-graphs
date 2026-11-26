//! Contact-centered interior shuffles followed by a boundary promotion.
//! Geometry generates candidates; actual forest connectivity decides legality.
use crate::certificate_corpus::{observe, Board, Forest, Observation};
use crate::neutral_search::{replay, Move, TraceStep};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::time::Instant;

#[derive(Clone, Debug, Serialize, Deserialize, Eq, PartialEq)]
pub struct Core {
    pub center: usize,
    pub deleted: [usize; 2],
    pub added: [usize; 2],
}
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Gain {
    pub before: Observation,
    pub core: Core,
    pub boundary: usize,
    pub trace: Vec<TraceStep>,
    pub after: Observation,
}
#[derive(Clone, Copy, Debug, Serialize, Deserialize, Eq, PartialEq)]
#[serde(rename_all = "snake_case")]
pub enum Status {
    Found,
    ExhaustedCandidates,
    TestLimit,
    TimeLimit,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Policy {
    pub interval: usize,
    pub stagnation: usize,
    pub test_limit: u64,
    pub time_limit_ms: u64,
}
impl Default for Policy {
    fn default() -> Self {
        Self {
            interval: 128,
            stagnation: 128,
            test_limit: 5000,
            time_limit_ms: 5,
        }
    }
}
#[derive(Default, Clone, Debug, Serialize, Deserialize)]
pub struct Stats {
    pub tests: u64,
    pub contacts: usize,
    pub geometric_candidates: usize,
    pub feasible_cores: usize,
    pub boundary_tests: usize,
    pub core_rejections: usize,
    pub boundary_rejections: usize,
    pub diagnostic_core_cycle_lengths: BTreeMap<usize, usize>,
    pub diagnostic_boundary_cycle_lengths: BTreeMap<usize, usize>,
    pub elapsed_seconds: f64,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Probe {
    pub schema: String,
    pub scope: String,
    pub status: Status,
    pub test_limit: u64,
    pub time_limit_ms: u64,
    pub diagnostics: bool,
    pub stats: Stats,
    pub gain: Option<Gain>,
}
pub fn boundary(n: usize, v: usize) -> bool {
    v % n == 0 || v % n + 1 == n || v / n == 0 || v / n + 1 == n
}
fn at(n: usize, x: isize, y: isize) -> Option<usize> {
    (x >= 0 && y >= 0 && x < n as isize && y < n as isize).then(|| y as usize * n + x as usize)
}
fn finish(mut p: Probe, status: Status, start: Instant) -> Probe {
    p.status = status;
    p.stats.elapsed_seconds = start.elapsed().as_secs_f64();
    p
}

/// At an interior U center m with opposite F neighbors m±axis, replace
/// those F vertices by m+side*perp and m-side*perp+2*end*axis. Both signs and
/// both axes are tried; all removed/inserted core vertices must be interior.
/// Only ORIGINAL boundary holes are tested for the subsequent gain.
pub fn probe(
    b: &Board,
    test_limit: u64,
    time_limit_ms: u64,
    diagnostics: bool,
) -> Result<Probe, String> {
    if !(1..=15).contains(&b.n) {
        return Err("shuffle search restricted to side 1..=15".into());
    }
    let start = Instant::now();
    let before = observe(b)?;
    let mut p = Probe {
        schema: "grid-graphs.boundary-shuffle-probe.v1".into(),
        scope: "bounded search of one specified shuffle class; exhaustion is not global optimality"
            .into(),
        status: Status::ExhaustedCandidates,
        test_limit,
        time_limit_ms,
        diagnostics,
        stats: Stats::default(),
        gain: None,
    };
    macro_rules! tick {
        () => {
            if p.stats.tests >= test_limit {
                return Ok(finish(p, Status::TestLimit, start));
            }
            if start.elapsed().as_millis() >= u128::from(time_limit_ms) {
                return Ok(finish(p, Status::TimeLimit, start));
            }
            p.stats.tests += 1;
        };
    }
    let holes: Vec<_> = (0..b.n * b.n)
        .filter(|&v| !b.preserved[v] && boundary(b.n, v))
        .collect();
    for center in 0..b.n * b.n {
        if b.preserved[center] {
            continue;
        }
        let (x, y) = ((center % b.n) as isize, (center / b.n) as isize);
        for (dx, dy) in [(0isize, 1isize), (1, 0)] {
            tick!();
            let (Some(a), Some(c)) = (at(b.n, x - dx, y - dy), at(b.n, x + dx, y + dy)) else {
                continue;
            };
            if !b.preserved[a] || !b.preserved[c] || boundary(b.n, a) || boundary(b.n, c) {
                continue;
            }
            p.stats.contacts += 1;
            let mut reduced = b.clone();
            reduced.preserved[a] = false;
            reduced.preserved[c] = false;
            let forest = Forest::from_board(&reduced)?;
            let (px, py) = (-dy, dx);
            for side in [-1isize, 1] {
                for end in [-1isize, 1] {
                    tick!();
                    let (Some(u), Some(v)) = (
                        at(b.n, x + side * px, y + side * py),
                        at(
                            b.n,
                            x - side * px + 2 * end * dx,
                            y - side * py + 2 * end * dy,
                        ),
                    ) else {
                        continue;
                    };
                    if b.preserved[u] || b.preserved[v] || boundary(b.n, u) || boundary(b.n, v) {
                        continue;
                    }
                    p.stats.geometric_candidates += 1;
                    let core = Core {
                        center,
                        deleted: [a, c],
                        added: [u, v],
                    };
                    let mut next = forest.clone();
                    if !next.insert(u) || !next.insert(v) {
                        p.stats.core_rejections += 1;
                        if diagnostics {
                            let mut bad = reduced.clone();
                            bad.preserved[u] = true;
                            bad.preserved[v] = true;
                            let length = crate::exchange_analysis::first_cycle_length(&bad)
                                .ok_or("missing rejection cycle")?;
                            *p.stats
                                .diagnostic_core_cycle_lengths
                                .entry(length)
                                .or_default() += 1;
                        }
                        continue;
                    }
                    p.stats.feasible_cores += 1;
                    for &w in &holes {
                        tick!();
                        p.stats.boundary_tests += 1;
                        if !next.can_insert(w) {
                            p.stats.boundary_rejections += 1;
                            if diagnostics {
                                let mut bad = reduced.clone();
                                for z in [u, v, w] {
                                    bad.preserved[z] = true;
                                }
                                let length = crate::exchange_analysis::first_cycle_length(&bad)
                                    .ok_or("missing rejection cycle")?;
                                *p.stats
                                    .diagnostic_boundary_cycle_lengths
                                    .entry(length)
                                    .or_default() += 1;
                            }
                            continue;
                        }
                        let mut neutral = reduced.clone();
                        neutral.preserved[u] = true;
                        neutral.preserved[v] = true;
                        let middle = observe(&neutral)?;
                        if middle.features["f"] != before.features["f"] {
                            return Err("shuffle changed neutral score".into());
                        }
                        let mut final_board = neutral.clone();
                        final_board.preserved[w] = true;
                        let after = observe(&final_board)?;
                        let trace = vec![
                            TraceStep {
                                exchange: Move {
                                    deleted: vec![a, c],
                                    added: vec![u, v],
                                },
                                rows: middle.rows,
                                f: before.features["f"],
                                missing_original_f: 2,
                            },
                            TraceStep {
                                exchange: Move {
                                    deleted: vec![],
                                    added: vec![w],
                                },
                                rows: after.rows.clone(),
                                f: before.features["f"] + 1,
                                missing_original_f: 2,
                            },
                        ];
                        replay(b, &trace, true)?;
                        p.gain = Some(Gain {
                            before,
                            core,
                            boundary: w,
                            trace,
                            after,
                        });
                        return Ok(finish(p, Status::Found, start));
                    }
                }
            }
        }
    }
    Ok(finish(p, Status::ExhaustedCandidates, start))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::neutral_search::Report;
    fn pregain(text: &str) -> Board {
        let r: Report = serde_json::from_str(text).unwrap();
        let b = Board::parse(&r.original.rows.join("\n")).unwrap();
        replay(&b, &r.trace, true).unwrap();
        Board::parse(&r.trace[r.trace.len() - 2].rows.join("\n")).unwrap()
    }
    #[test]
    fn both_recorded_gains_are_found_in_all_square_symmetries() {
        for text in [
            include_str!("../data/neutral_escape_14.json"),
            include_str!("../data/neutral_study_14/case_06.escape.json"),
        ] {
            let b = pregain(text);
            for f in crate::holdout_study::orbit(&b) {
                let transformed = Board {
                    n: 14,
                    preserved: f,
                };
                let p = probe(&transformed, 100_000, 10_000, true).unwrap();
                assert_eq!(p.status, Status::Found);
                let gain = p.gain.unwrap();
                assert_eq!(gain.after.features["f"], 77);
                assert_eq!(
                    replay(&transformed, &gain.trace, true).unwrap().rows,
                    gain.after.rows
                );
            }
        }
    }
    #[test]
    fn empty_class_and_cutoffs_are_distinct() {
        let b = Board {
            n: 6,
            preserved: vec![false; 36],
        };
        assert_eq!(probe(&b, 0, 1000, false).unwrap().status, Status::TestLimit);
        assert_eq!(
            probe(&b, 10000, 0, false).unwrap().status,
            Status::TimeLimit
        );
        assert_eq!(
            probe(&b, 10000, 1000, false).unwrap().status,
            Status::ExhaustedCandidates
        );
        assert!(probe(
            &Board {
                n: 17,
                preserved: vec![false; 289]
            },
            10000,
            1000,
            false
        )
        .is_err());
    }
    // Independent brute geometry: enumerate deletion and insertion PAIRS,
    // recognize the pattern by dot products, and validate whole final graphs.
    fn brute(b: &Board) -> bool {
        let f: Vec<_> = (0..b.n * b.n)
            .filter(|&v| b.preserved[v] && !boundary(b.n, v))
            .collect();
        let u: Vec<_> = (0..b.n * b.n)
            .filter(|&v| !b.preserved[v] && !boundary(b.n, v))
            .collect();
        let rim: Vec<_> = (0..b.n * b.n)
            .filter(|&v| !b.preserved[v] && boundary(b.n, v))
            .collect();
        for i in 0..f.len() {
            for &c in &f[i + 1..] {
                let a = f[i];
                let (ax, ay) = ((a % b.n) as isize, (a / b.n) as isize);
                let (cx, cy) = ((c % b.n) as isize, (c / b.n) as isize);
                if (ax - cx).abs() + (ay - cy).abs() != 2 || (ax != cx && ay != cy) {
                    continue;
                }
                let (mx, my) = ((ax + cx) / 2, (ay + cy) / 2);
                let center = my as usize * b.n + mx as usize;
                if b.preserved[center] {
                    continue;
                }
                let (dx, dy) = ((cx - ax) / 2, (cy - ay) / 2);
                let (px, py) = (-dy, dx);
                for j in 0..u.len() {
                    for &v in &u[j + 1..] {
                        let coords = |z: usize| {
                            let (x, y) = ((z % b.n) as isize - mx, (z / b.n) as isize - my);
                            (x * dx + y * dy, x * px + y * py)
                        };
                        let s = coords(u[j]);
                        let t = coords(v);
                        let matches = |s: (isize, isize), t: (isize, isize)| {
                            s.0 == 0 && s.1.abs() == 1 && t.0.abs() == 2 && t.1 == -s.1
                        };
                        if !matches(s, t) && !matches(t, s) {
                            continue;
                        }
                        for &w in &rim {
                            let mut trial = b.clone();
                            trial.preserved[a] = false;
                            trial.preserved[c] = false;
                            for z in [u[j], v, w] {
                                trial.preserved[z] = true;
                            }
                            if observe(&trial).is_ok() {
                                return true;
                            }
                        }
                    }
                }
            }
        }
        false
    }
    #[test]
    fn exhaustive_six_square_patch_matches_brute_pair_enumeration() {
        let positions: Vec<_> = (1..=4)
            .flat_map(|y| (1..=3).map(move |x| y * 6 + x))
            .collect();
        let mut positives = 0;
        let mut negatives = 0;
        for mask in 0u32..1 << 12 {
            let mut b = Board {
                n: 6,
                preserved: vec![false; 36],
            };
            for (i, &v) in positions.iter().enumerate() {
                b.preserved[v] = mask & (1 << i) != 0;
            }
            if observe(&b).is_err() {
                continue;
            }
            let expected = brute(&b);
            let p = probe(&b, 100_000, 10_000, false).unwrap();
            assert_eq!(p.status == Status::Found, expected, "patch={mask:x}");
            assert!(matches!(
                p.status,
                Status::Found | Status::ExhaustedCandidates
            ));
            if expected {
                positives += 1;
            } else {
                negatives += 1;
            }
        }
        assert!(positives > 0 && negatives > 0);
    }
}
