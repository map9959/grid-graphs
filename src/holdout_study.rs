//! Frozen, run-separated and symmetry-separated held-outs and equal-wall-time
//! search controls. Selection never consults subsequent benchmark outcomes.
use crate::certificate_corpus::{observe, sample, Board};
use crate::neutral_search::{replay, search, Config, Report};
use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;
use std::time::Instant;

pub fn orbit(b: &Board) -> Vec<Vec<bool>> {
    (0..8)
        .map(|symmetry| {
            let mut f = vec![false; b.n * b.n];
            for y in 0..b.n {
                for x in 0..b.n {
                    let (mut yy, mut xx) = (y, x);
                    if symmetry >= 4 {
                        xx = b.n - 1 - xx;
                    }
                    for _ in 0..symmetry % 4 {
                        (yy, xx) = (xx, b.n - 1 - yy);
                    }
                    f[yy * b.n + xx] = b.preserved[y * b.n + x];
                }
            }
            f
        })
        .collect()
}
pub fn canonical(b: &Board) -> Vec<bool> {
    orbit(b).into_iter().min().unwrap()
}
fn separation(a: &Board, b: &Board) -> usize {
    orbit(b)
        .iter()
        .map(|f| {
            a.preserved
                .iter()
                .zip(f)
                .filter(|(x, y)| **x && !**y)
                .count()
        })
        .min()
        .unwrap()
}

#[derive(Clone, Serialize, Deserialize)]
pub struct Candidate {
    pub source_id: usize,
    pub family: String,
    pub source_seed: u64,
    pub observed_f: i64,
    pub rows: Vec<String>,
}
#[derive(Clone, Serialize, Deserialize)]
pub struct Input {
    pub id: usize,
    pub source_id: usize,
    pub min_symmetry_distance_at_selection: usize,
}
#[derive(Serialize, Deserialize)]
pub struct Manifest {
    pub schema: String,
    pub scope: String,
    pub n: usize,
    pub generation_iterations: usize,
    pub generation_first_seed: u64,
    pub generation_algorithm: String,
    pub parallel_initial_rows: Vec<String>,
    pub forbidden_training_rows: Vec<Vec<String>>,
    pub candidates: Vec<Candidate>,
    pub inputs: Vec<Input>,
}
impl Manifest {
    pub fn validate(&self) -> Result<(), String> {
        if self.schema != "grid-graphs.neutral-heldout-manifest.v1"
            || self.n != 14
            || self.inputs.len() != 8
            || self.candidates.len() != 24
            || self.generation_iterations != 10_000
            || self.generation_first_seed != 20261001
        {
            return Err("unexpected held-out protocol".into());
        }
        let training: Report = serde_json::from_str(include_str!("../data/neutral_escape_14.json"))
            .map_err(|e| e.to_string())?;
        let mut expected_rows = vec![training.original.rows.clone()];
        expected_rows.extend(training.trace.iter().map(|s| s.rows.clone()));
        if self.forbidden_training_rows != expected_rows
            || self.parallel_initial_rows
                != Board::parse(include_str!("../data/corpus_seed_parallel_14.txt"))?.rows()
            || self.generation_algorithm != "primal-star-delete-regrow-splitmix64-v1"
        {
            return Err("training exclusions or generation setup changed".into());
        }
        let forbidden = self
            .forbidden_training_rows
            .iter()
            .map(|rows| {
                let b = Board::parse(&rows.join("\n"))?;
                observe(&b)?;
                if b.n != 14 {
                    return Err("training size mismatch".into());
                }
                Ok(canonical(&b))
            })
            .collect::<Result<BTreeSet<_>, String>>()?;
        let mut seen = BTreeSet::new();
        let mut ids = BTreeSet::new();
        let mut family_counts = [0usize; 2];
        let mut references = vec![Board::parse(&self.forbidden_training_rows[0].join("\n"))?];
        for (i, c) in self.candidates.iter().enumerate() {
            let b = Board::parse(&c.rows.join("\n"))?;
            if c.source_id != i
                || c.source_seed != self.generation_first_seed + i as u64
                || c.family != if i < 12 { "unseeded" } else { "parallel_rods" }
                || b.n != 14
                || observe(&b)?.features["f"] != c.observed_f
            {
                return Err("candidate provenance or observation mismatch".into());
            }
        }
        for (i, input) in self.inputs.iter().enumerate() {
            let c = self
                .candidates
                .get(input.source_id)
                .ok_or("invalid source ID")?;
            let b = Board::parse(&c.rows.join("\n"))?;
            let key = canonical(&b);
            let actual_distance = references.iter().map(|r| separation(r, &b)).min().unwrap();
            if input.id != i
                || c.observed_f != 76
                || c.family
                    != if i % 2 == 0 {
                        "unseeded"
                    } else {
                        "parallel_rods"
                    }
                || !ids.insert(input.source_id)
                || forbidden.contains(&key)
                || !seen.insert(key)
                || input.min_symmetry_distance_at_selection != actual_distance
            {
                return Err("held-out score, run, or symmetry exclusion violated".into());
            }
            family_counts[usize::from(c.family == "parallel_rods")] += 1;
            references.push(b);
        }
        if family_counts != [4, 4] {
            return Err("expected four inputs from each starting family".into());
        }
        Ok(())
    }
    pub fn board(&self, index: usize) -> Result<Board, String> {
        let input = self.inputs.get(index).ok_or("invalid held-out index")?;
        Board::parse(&self.candidates[input.source_id].rows.join("\n"))
    }
}

pub fn select() -> Result<Manifest, String> {
    let training: Report = serde_json::from_str(include_str!("../data/neutral_escape_14.json"))
        .map_err(|e| e.to_string())?;
    let original = Board::parse(&training.original.rows.join("\n"))?;
    replay(&original, &training.trace, true)?;
    let mut forbidden_rows = vec![training.original.rows.clone()];
    forbidden_rows.extend(training.trace.iter().map(|s| s.rows.clone()));
    let forbidden: BTreeSet<_> = forbidden_rows
        .iter()
        .map(|r| canonical(&Board::parse(&r.join("\n")).unwrap()))
        .collect();
    let parallel = Board::parse(include_str!("../data/corpus_seed_parallel_14.txt"))?;
    observe(&parallel)?;
    let mut candidates = Vec::new();
    for i in 0..24 {
        let seed = 20261001 + i as u64;
        let o = sample(
            14,
            10_000,
            seed,
            if i < 12 { None } else { Some(&parallel) },
        )?;
        candidates.push(Candidate {
            source_id: i,
            source_seed: seed,
            family: if i < 12 { "unseeded" } else { "parallel_rods" }.into(),
            observed_f: o.features["f"],
            rows: o.rows,
        });
    }
    let boards = candidates
        .iter()
        .map(|c| Board::parse(&c.rows.join("\n")))
        .collect::<Result<Vec<_>, _>>()?;
    let mut picked = Vec::new();
    let mut selected_boards = vec![original];
    let mut used = forbidden;
    let mut shapes = BTreeSet::new();
    for id in 0..8 {
        let family = if id % 2 == 0 {
            "unseeded"
        } else {
            "parallel_rods"
        };
        let choice = candidates
            .iter()
            .enumerate()
            .filter(|(i, c)| {
                c.observed_f == 76 && c.family == family && !used.contains(&canonical(&boards[*i]))
            })
            .map(|(i, c)| {
                let o = observe(&boards[i]).unwrap();
                let shape = [
                    o.features["c"],
                    o.features["z"],
                    o.features["r"],
                    o.features["b"],
                ];
                let d = selected_boards
                    .iter()
                    .map(|b| separation(b, &boards[i]))
                    .min()
                    .unwrap();
                (
                    i,
                    d,
                    shape,
                    (!shapes.contains(&shape), d, u64::MAX - c.source_seed),
                )
            })
            .max_by_key(|x| x.3)
            .ok_or("not enough fresh score-76 symmetry classes in the declared pool")?;
        let (i, d, shape, _) = choice;
        used.insert(canonical(&boards[i]));
        shapes.insert(shape);
        selected_boards.push(boards[i].clone());
        picked.push(Input {
            id,
            source_id: i,
            min_symmetry_distance_at_selection: d,
        });
    }
    let manifest=Manifest {schema:"grid-graphs.neutral-heldout-manifest.v1".into(),n:14,
        scope:"eight inputs chosen before benchmarking from 24 fresh source runs; four per starting family; no training-trace symmetry duplicates; not an IID population sample".into(),
        generation_iterations:10_000,generation_first_seed:20261001,
        generation_algorithm:"primal-star-delete-regrow-splitmix64-v1".into(),parallel_initial_rows:parallel.rows(),
        forbidden_training_rows:forbidden_rows,candidates,inputs:picked};
    manifest.validate()?;
    Ok(manifest)
}

#[derive(Serialize)]
pub struct NeutralBudget {
    pub scope: String,
    pub time_budget_ms: u64,
    pub use_certified_radius: bool,
    pub seed: u64,
    pub success: bool,
    pub first_target_seconds: Option<f64>,
    pub wall_seconds: f64,
    pub stop_reason: String,
    pub attempts: Vec<Report>,
}

/// Restart deterministic one-for-one beams with fresh tie seeds when depth or
/// state limits end an attempt. The ENTIRE arm, not each restart, gets the
/// specified wall budget. Bounds are disabled explicitly on held-out arms.
pub fn neutral_timed(
    b: &Board,
    seed: u64,
    milliseconds: u64,
    use_bound: bool,
) -> Result<NeutralBudget, String> {
    if !(1..=15).contains(&b.n) || milliseconds > 60_000 {
        return Err("invalid benchmark size/time bound".into());
    }
    observe(b)?;
    let started = Instant::now();
    let mut attempts = Vec::new();
    let mut found = None;
    let mut reason = "time_limit";
    while started.elapsed().as_millis() < u128::from(milliseconds) && attempts.len() < 64 {
        let remaining = milliseconds.saturating_sub(started.elapsed().as_millis() as u64);
        if remaining == 0 {
            break;
        }
        let cfg = Config {
            seed: seed.wrapping_add(attempts.len() as u64),
            time_limit_ms: remaining,
            use_certified_radius: use_bound,
            ..Config::default()
        };
        let report = search(b, cfg)?;
        if !use_bound && report.original_excluded_deletion_radius.is_some() {
            return Err("benchmark inherited forbidden pruning".into());
        }
        let success = report.status == "escape_found";
        let no_seed_effect = report.status == "frontier_empty" && report.stats.beam_discarded == 0;
        attempts.push(report);
        if success {
            found = Some(started.elapsed().as_secs_f64());
            reason = "target_found";
            break;
        }
        if no_seed_effect {
            reason = "no_seed_dependent_frontier";
            break;
        }
    }
    if found.is_none() && attempts.len() == 64 {
        reason = "restart_limit";
    }
    Ok(NeutralBudget {
        scope:
            "equal-wall-time one-for-one beam arm with fresh-seed restarts; not exact optimization"
                .into(),
        time_budget_ms: milliseconds,
        use_certified_radius: use_bound,
        seed,
        success: found.is_some(),
        first_target_seconds: found,
        wall_seconds: started.elapsed().as_secs_f64(),
        stop_reason: reason.into(),
        attempts,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn frozen_selection_rejects_training_leakage_and_duplicate_runs() {
        let text = include_str!("../data/neutral_study_14/selection.json");
        let mut manifest: Manifest = serde_json::from_str(text).unwrap();
        manifest.validate().unwrap();
        manifest.inputs[2].source_id = manifest.inputs[0].source_id;
        assert!(manifest.validate().is_err());
        let mut manifest: Manifest = serde_json::from_str(text).unwrap();
        let id = manifest.inputs[0].source_id;
        manifest.candidates[id].rows = manifest.forbidden_training_rows[0].clone();
        assert!(manifest.validate().is_err());
        let mut manifest: Manifest = serde_json::from_str(text).unwrap();
        manifest.inputs[0].min_symmetry_distance_at_selection += 1;
        assert!(manifest.validate().is_err());
    }

    #[test]
    fn heldout_escape_matches_its_input_and_has_no_certified_pruning() {
        let manifest: Manifest =
            serde_json::from_str(include_str!("../data/neutral_study_14/selection.json")).unwrap();
        let r: Report =
            serde_json::from_str(include_str!("../data/neutral_study_14/case_06.escape.json"))
                .unwrap();
        let b = manifest.board(6).unwrap();
        assert_eq!(r.original.rows, b.rows());
        assert!(!r.config.use_certified_radius);
        assert_eq!(r.original_excluded_deletion_radius, None);
        assert_eq!(replay(&b, &r.trace, true).unwrap().features["f"], 77);
    }
    #[test]
    fn symmetry_keys_and_distance_are_not_orientation_dependent() {
        let b = Board::parse(".UU\nUUU\nU.U").unwrap();
        for f in orbit(&b) {
            let r = Board { n: 3, preserved: f };
            assert_eq!(canonical(&b), canonical(&r));
            assert_eq!(separation(&b, &r), 0);
        }
    }
    #[test]
    fn unpruned_budget_and_time_zero_are_explicit() {
        let b = Board::parse("UU\nUU").unwrap();
        let zero = neutral_timed(&b, 1, 0, false).unwrap();
        assert!(!zero.success);
        assert!(zero.attempts.is_empty());
        let r = neutral_timed(&b, 1, 1000, false).unwrap();
        assert!(r.success);
        assert_eq!(r.attempts[0].original_excluded_deletion_radius, None);
        assert!(!r.attempts[0].config.use_certified_radius);
        assert!(neutral_timed(
            &Board {
                n: 17,
                preserved: vec![false; 289]
            },
            1,
            1000,
            false
        )
        .is_err());
    }
}
