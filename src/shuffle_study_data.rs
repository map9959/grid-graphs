//! A fresh frozen selection for the sampler/operator comparison.
use crate::boundary_shuffle::Policy;
use crate::certificate_corpus::{observe, sample, Board};
use crate::holdout_study::{canonical, orbit, Candidate, Input};
use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::{collections::BTreeSet, fs, path::Path};

fn collect_rows(value: &Value, seen: &mut BTreeSet<Vec<bool>>) -> Result<(), String> {
    match value {
        Value::Object(map) => {
            if let Some(Value::Array(rows)) = map.get("rows") {
                if rows.len() == 14 && rows.iter().all(Value::is_string) {
                    let text = rows
                        .iter()
                        .map(|x| x.as_str().unwrap())
                        .collect::<Vec<_>>()
                        .join("\n");
                    let b = Board::parse(&text)?;
                    observe(&b)?;
                    seen.insert(canonical(&b));
                }
            }
            for v in map.values() {
                collect_rows(v, seen)?;
            }
        }
        Value::Array(values) => {
            for v in values {
                collect_rows(v, seen)?;
            }
        }
        _ => (),
    }
    Ok(())
}
pub fn recorded_exclusions(prior: &Path) -> Result<Vec<Vec<String>>, String> {
    let mut seen = BTreeSet::new();
    let training: Value = serde_json::from_str(include_str!("../data/neutral_escape_14.json"))
        .map_err(|e| e.to_string())?;
    collect_rows(&training, &mut seen)?;
    for entry in fs::read_dir(prior).map_err(|e| e.to_string())? {
        let path = entry.map_err(|e| e.to_string())?.path();
        if path.extension().and_then(|s| s.to_str()) != Some("json") {
            continue;
        }
        let value: Value =
            serde_json::from_str(&fs::read_to_string(path).map_err(|e| e.to_string())?)
                .map_err(|e| e.to_string())?;
        collect_rows(&value, &mut seen)?;
    }
    Ok(seen
        .into_iter()
        .map(|f| {
            Board {
                n: 14,
                preserved: f,
            }
            .rows()
        })
        .collect())
}
fn separation(a: &Board, b: &Board) -> usize {
    orbit(b)
        .iter()
        .map(|f| {
            a.preserved
                .iter()
                .zip(f)
                .filter(|(a, b)| **a && !**b)
                .count()
        })
        .min()
        .unwrap()
}
#[derive(Serialize, Deserialize)]
pub struct Manifest {
    pub schema: String,
    pub scope: String,
    pub generation_first_seed: u64,
    pub generation_iterations: usize,
    pub prior_directory: String,
    pub excluded_rows: Vec<Vec<String>>,
    pub policy: Policy,
    pub candidates: Vec<Candidate>,
    pub inputs: Vec<Input>,
}
impl Manifest {
    pub fn validate(&self) -> Result<(), String> {
        if self.schema != "grid-graphs.shuffle-heldout-manifest.v1"
            || self.generation_first_seed != 20261201
            || self.generation_iterations != 10_000
            || self.candidates.len() != 24
            || self.inputs.len() != 8
            || self.policy.interval != 128
            || self.policy.stagnation != 128
            || self.policy.test_limit != 5000
            || self.policy.time_limit_ms != 5
        {
            return Err("operator protocol mismatch".into());
        }
        let actual_exclusions = recorded_exclusions(Path::new(&self.prior_directory))?;
        if actual_exclusions != self.excluded_rows {
            return Err("prior recorded exclusions changed".into());
        }
        let excluded = self
            .excluded_rows
            .iter()
            .map(|r| Board::parse(&r.join("\n")).map(|b| canonical(&b)))
            .collect::<Result<BTreeSet<_>, _>>()?;
        let mut references = self
            .excluded_rows
            .iter()
            .map(|r| Board::parse(&r.join("\n")))
            .collect::<Result<Vec<_>, _>>()?;
        references.retain(|b| b.preserved.iter().filter(|&&f| f).count() == 76);
        if references.is_empty() {
            return Err("missing development references".into());
        }
        let mut used = BTreeSet::new();
        let mut source_ids = BTreeSet::new();
        for (i, c) in self.candidates.iter().enumerate() {
            let b = Board::parse(&c.rows.join("\n"))?;
            if c.source_id != i
                || c.source_seed != self.generation_first_seed + i as u64
                || c.family != if i < 12 { "unseeded" } else { "parallel_rods" }
                || b.n != 14
                || observe(&b)?.features["f"] != c.observed_f
            {
                return Err("candidate record mismatch".into());
            }
        }
        for (i, input) in self.inputs.iter().enumerate() {
            let c = self
                .candidates
                .get(input.source_id)
                .ok_or("bad source ID")?;
            let b = Board::parse(&c.rows.join("\n"))?;
            let key = canonical(&b);
            if input.id != i
                || c.family
                    != if i % 2 == 0 {
                        "unseeded"
                    } else {
                        "parallel_rods"
                    }
                || c.observed_f != 76
                || excluded.contains(&key)
                || !used.insert(key)
                || !source_ids.insert(input.source_id)
                || references.iter().map(|r| separation(r, &b)).min().unwrap()
                    != input.min_symmetry_distance_at_selection
            {
                return Err("selection score, source, symmetry, or distance mismatch".into());
            }
            references.push(b);
        }
        Ok(())
    }
    pub fn board(&self, i: usize) -> Result<Board, String> {
        let input = self.inputs.get(i).ok_or("input index outside 0..8")?;
        Board::parse(&self.candidates[input.source_id].rows.join("\n"))
    }
}
pub fn select(prior: &Path) -> Result<Manifest, String> {
    let excluded_rows = recorded_exclusions(prior)?;
    let mut references = excluded_rows
        .iter()
        .map(|r| Board::parse(&r.join("\n")))
        .collect::<Result<Vec<_>, _>>()?;
    let mut used: BTreeSet<_> = references.iter().map(canonical).collect();
    references.retain(|b| b.preserved.iter().filter(|&&f| f).count() == 76);
    if references.is_empty() {
        return Err("no development references".into());
    }
    let parallel = Board::parse(include_str!("../data/corpus_seed_parallel_14.txt"))?;
    let mut candidates = Vec::new();
    for i in 0..24 {
        let seed = 20261201 + i as u64;
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
    let mut inputs = Vec::new();
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
                c.family == family && c.observed_f == 76 && !used.contains(&canonical(&boards[*i]))
            })
            .map(|(i, c)| {
                let o = observe(&boards[i]).unwrap();
                let shape = [
                    o.features["r"],
                    o.features["b"],
                    o.features["c"],
                    o.features["z"],
                ];
                let d = references
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
            .ok_or("declared candidate pool has too few eligible inputs")?;
        let (i, d, shape, _) = choice;
        used.insert(canonical(&boards[i]));
        shapes.insert(shape);
        references.push(boards[i].clone());
        inputs.push(Input {
            id,
            source_id: i,
            min_symmetry_distance_at_selection: d,
        });
    }
    let manifest=Manifest {schema:"grid-graphs.shuffle-heldout-manifest.v1".into(),
        scope:"fresh source runs, score-76 and symmetry-separated from recorded prior study states; selected before benchmarking, not an IID sample".into(),
        generation_first_seed:20261201,generation_iterations:10_000,prior_directory:prior.to_string_lossy().into(),
        excluded_rows,policy:Policy::default(),candidates,inputs};
    manifest.validate()?;
    Ok(manifest)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn frozen_operator_selection_rejects_leakage_duplicates_and_policy_changes() {
        let text = include_str!("../data/shuffle_study_14/selection.json");
        let m: Manifest = serde_json::from_str(text).unwrap();
        m.validate().unwrap();
        assert_eq!(m.excluded_rows.len(), 300);
        let mut changed: Manifest = serde_json::from_str(text).unwrap();
        changed.inputs[2].source_id = changed.inputs[0].source_id;
        assert!(changed.validate().is_err());
        let mut changed: Manifest = serde_json::from_str(text).unwrap();
        changed.policy.interval = 64;
        assert!(changed.validate().is_err());
        let mut changed: Manifest = serde_json::from_str(text).unwrap();
        let rows = changed
            .excluded_rows
            .iter()
            .find(|r| {
                let b = Board::parse(&r.join("\n")).unwrap();
                b.preserved.iter().filter(|&&f| f).count() == 76
            })
            .unwrap()
            .clone();
        let i = changed.inputs[0].source_id;
        changed.candidates[i].rows = rows;
        assert!(changed.validate().is_err());
    }
}
