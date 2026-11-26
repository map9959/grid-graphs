//! Bounded corpus discovery and independent witness/linear-claim checking.
use anyhow::{anyhow, bail, Context, Result};
use grid_graphs::certificate_corpus::{observe, sample, sample_trace, Board, Observation};
use grid_graphs::exchange_analysis::{diagnose, repair, scan};
use rayon::prelude::*;
use serde::Deserialize;
use serde_json::{json, Value};
use std::{
    collections::BTreeMap,
    env, fs,
    io::{self, Write},
};

fn load(path: &str) -> Result<Board> {
    Board::parse(&fs::read_to_string(path).with_context(|| format!("reading {path}"))?)
        .map_err(|e| anyhow!("{path}: {e}"))
}
fn number<T: std::str::FromStr>(s: &str) -> Result<T> {
    s.parse()
        .map_err(|_| anyhow!("invalid numeric argument: {s}"))
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Claim {
    constant: i64,
    coefficients: BTreeMap<String, i64>,
}

fn check_claim(corpus: &Value, claim: &Claim) -> Result<Value> {
    let observations = corpus
        .get("observations")
        .and_then(Value::as_array)
        .ok_or_else(|| anyhow!("expected a sample/enumerate corpus"))?;
    if observations.is_empty() {
        bail!("empty corpus");
    }
    let mut minimum = i128::MAX;
    let mut worst = None;
    for value in observations {
        let recorded: Observation = serde_json::from_value(value.clone())?;
        let b = Board::parse(&recorded.rows.join("\n")).map_err(|e| anyhow!(e))?;
        let actual = observe(&b).map_err(|e| anyhow!(e))?;
        if actual.features != recorded.features || actual.local_3x3 != recorded.local_3x3 {
            bail!("corpus feature mismatch: witnesses must be independently replayable");
        }
        let mut slack = i128::from(claim.constant);
        for (name, coefficient) in &claim.coefficients {
            let value = if let Some(mask) = name.strip_prefix("local3:") {
                let index: usize = number(mask)?;
                i64::from(
                    *actual
                        .local_3x3
                        .get(index)
                        .ok_or_else(|| anyhow!("invalid local3 mask"))?,
                )
            } else {
                *actual
                    .features
                    .get(name)
                    .ok_or_else(|| anyhow!("unknown feature {name}"))?
            };
            slack = slack
                .checked_add(i128::from(*coefficient) * i128::from(value))
                .ok_or_else(|| anyhow!("claim arithmetic overflow"))?;
        }
        if slack < minimum {
            minimum = slack;
            worst = Some(actual);
        }
    }
    Ok(json!({"schema": "grid-graphs.corpus-claim-check.v1",
        "meaning": "constant + sum(coefficient * feature) >= 0",
        "scope": "finite corpus check, not a universal certificate",
        "observations_checked": observations.len(), "falsified": minimum < 0,
        "minimum_slack": minimum.to_string(), "worst_observation": worst}))
}

fn compare(args: &[String]) -> Result<Value> {
    let n: usize = number(&args[1])?;
    let iterations: usize = number(&args[2])?;
    let runs: usize = number(&args[3])?;
    let seed: u64 = number(&args[4])?;
    let node_limit: usize = number(&args[5])?;
    if !(1..=15).contains(&n) || !(1..=64).contains(&runs) {
        bail!("compare requires side 1..=15 and runs 1..=64");
    }
    if args.len() > 14 {
        bail!("at most eight seed files");
    }
    let mut starts = vec![(None, None)];
    for path in &args[6..] {
        let board = load(path)?;
        if board.n != n {
            bail!("seed size mismatch: {path}");
        }
        observe(&board).map_err(|e| anyhow!(e))?;
        starts.push((Some(path.clone()), Some(board)));
    }
    let pool = rayon::ThreadPoolBuilder::new().num_threads(2).build()?;
    let mut variants = Vec::new();
    let mut corpus = BTreeMap::new();
    for (path, initial) in starts {
        for guided in [false, true] {
            let started = std::time::Instant::now();
            let traces: Vec<_> = pool.install(|| {
                (0..runs)
                    .into_par_iter()
                    .map(|i| {
                        sample_trace(
                            n,
                            iterations,
                            seed.wrapping_add(i as u64),
                            initial.as_ref(),
                            guided.then_some(node_limit),
                        )
                    })
                    .collect()
            });
            let elapsed = started.elapsed().as_secs_f64();
            let mut records = Vec::new();
            let mut histogram = BTreeMap::<i64, usize>::new();
            let mut observed_scores = BTreeMap::<i64, usize>::new();
            let mut distinct_best = std::collections::BTreeSet::new();
            for (i, trace) in traces.into_iter().enumerate() {
                let trace = trace.map_err(|e| anyhow!(e))?;
                *histogram.entry(trace.best.features["f"]).or_default() += 1;
                distinct_best.insert(trace.best.rows.clone());
                let mut run_rows = Vec::new();
                for o in trace.near_optimal {
                    *observed_scores.entry(o.features["f"]).or_default() += 1;
                    run_rows.push(o.rows.clone());
                    corpus.entry(o.rows.clone()).or_insert(o);
                }
                records.push(json!({"seed": seed.wrapping_add(i as u64),
                    "best_rows": trace.best.rows, "stats": trace.stats,
                    "archived_rows": run_rows}));
                corpus.entry(trace.best.rows.clone()).or_insert(trace.best);
            }
            variants.push(
                json!({"start": path, "initial_rows": initial.as_ref().map(Board::rows),
                "policy": if guided {"cycle_guided_v1"} else {"random_v1"},
                "wall_seconds": elapsed, "iterations_per_run": iterations,
                "best_f": histogram.keys().next_back(), "best_histogram": histogram,
                "distinct_best_witnesses": distinct_best.len(),
                "archived_score_histogram_with_run_multiplicity": observed_scores,
                "runs": records}),
            );
        }
    }
    Ok(
        json!({"schema": "grid-graphs.certificate-corpus.v1", "mode": "compare",
        "scope": "heuristic comparison at equal iteration counts, not equal time or exact optimization",
        "algorithm": "primal-cycle-guided-comparison-v1", "n": n, "first_seed": seed,
        "runs_per_variant": runs, "threads": 2, "repair_nodes_per_proposal": node_limit,
        "repair_max_deletions": 3, "archive_margin_from_run_best": 2,
        "archive_limit_per_score_per_run": 8, "variants": variants,
        "observations": corpus.into_values().collect::<Vec<_>>()}),
    )
}

fn summarize(corpus: &Value) -> Result<Value> {
    // Replay all exported witnesses before describing this artifact.
    let checked = check_claim(
        corpus,
        &Claim {
            constant: 0,
            coefficients: BTreeMap::new(),
        },
    )?;
    let variants = corpus["variants"]
        .as_array()
        .ok_or_else(|| anyhow!("expected compare output"))?;
    let mut summaries = Vec::new();
    for variant in variants {
        let mut summary = serde_json::Map::new();
        for key in [
            "start",
            "policy",
            "best_f",
            "best_histogram",
            "distinct_best_witnesses",
            "wall_seconds",
        ] {
            summary.insert(key.into(), variant[key].clone());
        }
        let runs = variant["runs"]
            .as_array()
            .ok_or_else(|| anyhow!("missing run records"))?;
        for key in [
            "repair_attempts",
            "repair_nodes",
            "repair_successes",
            "repair_cutoffs",
            "repair_exhausted",
        ] {
            let total = runs.iter().try_fold(0u64, |sum, r| {
                let value = r["stats"][key]
                    .as_u64()
                    .ok_or_else(|| anyhow!("invalid {key}"))?;
                sum.checked_add(value)
                    .ok_or_else(|| anyhow!("counter overflow"))
            })?;
            summary.insert(key.into(), json!(total));
        }
        summaries.push(Value::Object(summary));
    }
    Ok(
        json!({"schema": "grid-graphs.exchange-comparison-summary.v1",
        "scope": "witnesses replayed; timing and run counters summarized, not independently reproduced",
        "n": corpus["n"], "first_seed": corpus["first_seed"],
        "runs_per_variant": corpus["runs_per_variant"],
        "repair_nodes_per_proposal": corpus["repair_nodes_per_proposal"],
        "observations_replayed": checked["observations_checked"], "variants": summaries}),
    )
}
fn run(args: &[String]) -> Result<Value> {
    match args.first().map(String::as_str) {
        Some("delete-first") if args.len() == 5 => {
            let report = grid_graphs::deletion_search::search(&load(&args[1])?,
                number(&args[2])?, number(&args[3])?, number(&args[4])?)
                .map_err(|e| anyhow!(e))?;
            Ok(serde_json::to_value(report)?)
        }
        Some("diagnose") if args.len() == 2 => {
            let report = diagnose(&load(&args[1])?).map_err(|e| anyhow!(e))?;
            Ok(serde_json::to_value(report)?)
        }
        Some("repair") if args.len() >= 5 => {
            let board = load(&args[1])?;
            let max_deletions = number(&args[2])?;
            let node_limit = number(&args[3])?;
            let adds = args[4..].iter().map(|s| number(s)).collect::<Result<Vec<usize>>>()?;
            let report = repair(&board, &adds, max_deletions, node_limit).map_err(|e| anyhow!(e))?;
            Ok(json!({"schema": "grid-graphs.fixed-addition-repair.v1",
                "scope": "minimum deletions for these fixed additions within the stated budgets only",
                "vertex_numbering": "row-major zero-based: vertex=y*n+x",
                "original": observe(&board).map_err(|e| anyhow!(e))?, "repair": report}))
        }
        Some("compare") if args.len() >= 6 => compare(args),
        Some("scan") if args.len() == 5 => {
            let board = load(&args[1])?;
            let report = scan(&board, number(&args[2])?, number(&args[3])?, number(&args[4])?)
                .map_err(|e| anyhow!(e))?;
            Ok(serde_json::to_value(report)?)
        }
        Some("summarize") if args.len() == 2 => {
            summarize(&serde_json::from_str(&fs::read_to_string(&args[1])?)?)
        }
        Some("verify") if args.len() >= 2 => {
            let mut records = Vec::new();
            for path in &args[1..] {
                let board = load(path)?;
                let observation = observe(&board).map_err(|e| anyhow!("{path}: {e}"))?;
                records.push(json!({"path": path, "observation": observation}));
            }
            Ok(json!({"schema": "grid-graphs.certificate-corpus.v1", "mode": "verify",
                "scope": "literal witness validation only; no optimality claim", "records": records}))
        }
        Some("sample") if args.len() == 5 || args.len() == 6 => {
            let n: usize = number(&args[1])?;
            let iterations: usize = number(&args[2])?;
            let runs: usize = number(&args[3])?;
            let seed: u64 = number(&args[4])?;
            if !(1..=15).contains(&n) { bail!("sampling is restricted to side 1..=15"); }
            if !(1..=4096).contains(&runs) { bail!("runs must be in 1..=4096"); }
            let initial = args.get(5).map(|p| load(p)).transpose()?;
            if let Some(b) = &initial {
                if b.n != n { bail!("seed size mismatch"); }
                observe(b).map_err(|e| anyhow!(e))?;
            }
            let pool = rayon::ThreadPoolBuilder::new().num_threads(2).build()?;
            let results: Vec<_> = pool.install(|| (0..runs).into_par_iter().map(|i| {
                sample(n, iterations, seed.wrapping_add(i as u64), initial.as_ref())
            }).collect());
            let mut observations = Vec::new();
            let mut histogram = BTreeMap::<i64, usize>::new();
            for result in results {
                let observation = result.map_err(|e| anyhow!(e))?;
                *histogram.entry(observation.features["f"]).or_default() += 1;
                observations.push(observation);
            }
            let distinct = observations.iter().map(|o| &o.rows)
                .collect::<std::collections::BTreeSet<_>>().len();
            Ok(json!({"schema": "grid-graphs.certificate-corpus.v1", "mode": "sample",
                "scope": "heuristic lower bounds and finite falsification only; never UNSAT",
                "algorithm": "primal-star-delete-regrow-splitmix64-v1", "n": n,
                "iterations_per_run": iterations, "runs": runs, "first_seed": seed,
                "threads": 2, "initial_rows": initial.map(|b| b.rows()),
                "best_f": histogram.keys().next_back(), "distinct_witnesses": distinct,
                "run_best_histogram": histogram,
                "observations": observations}))
        }
        Some("enumerate") if args.len() == 2 => {
            let n: usize = number(&args[1])?;
            if !(1..=4).contains(&n) { bail!("exhaustive enumeration is restricted to side 1..=4"); }
            let total = 1u64 << (n*n);
            let mut histogram = BTreeMap::<i64, usize>::new();
            let mut observations = Vec::new();
            let mut best = -1;
            for mask in 0..total {
                let b = Board { n, preserved: (0..n*n).map(|v| mask & (1<<v) != 0).collect() };
                if let Ok(o) = observe(&b) {
                    let f = o.features["f"];
                    *histogram.entry(f).or_default() += 1;
                    if f > best { best = f; observations.clear(); }
                    if f == best && observations.len() < 128 { observations.push(o); }
                }
            }
            Ok(json!({"schema": "grid-graphs.certificate-corpus.v1", "mode": "enumerate",
                "scope": "complete enumeration for this board size only",
                "n": n, "subsets_examined": total, "complete": true, "best_f": best,
                "feasible_histogram": histogram, "optimal_witness_limit": 128,
                "observations": observations}))
        }
        Some("check-claim") if args.len() == 3 => {
            let corpus: Value = serde_json::from_str(&fs::read_to_string(&args[1])?)?;
            let claim: Claim = serde_json::from_str(&fs::read_to_string(&args[2])?)?;
            check_claim(&corpus, &claim)
        }
        _ => bail!("usage:\n  certificate_corpus verify U_WITNESS...\n  certificate_corpus diagnose U_WITNESS\n  certificate_corpus repair U_WITNESS MAX_DELETE MAX_NODES ADD_VERTEX...\n  certificate_corpus scan U_WITNESS ADD_COUNT MAX_NODES_PER_QUERY MAX_QUERIES\n  certificate_corpus delete-first U_WITNESS DELETE_COUNT MAX_NODES MAX_MILLISECONDS\n  certificate_corpus compare N ITERATIONS RUNS SEED REPAIR_NODES [U_WITNESS...]\n  certificate_corpus summarize COMPARISON_JSON\n  certificate_corpus sample N ITERATIONS RUNS SEED [U_WITNESS]\n  certificate_corpus enumerate N\n  certificate_corpus check-claim CORPUS_JSON CLAIM_JSON"),
    }
}
fn main() -> Result<()> {
    let result = run(&env::args().skip(1).collect::<Vec<_>>())?;
    let mut out = io::BufWriter::new(io::stdout().lock());
    serde_json::to_writer_pretty(&mut out, &result)?;
    writeln!(out)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn enumerate_and_sampling_reports_have_distinct_scopes() {
        let args = |s: &str| s.split_whitespace().map(String::from).collect::<Vec<_>>();
        let exact = run(&args("enumerate 3")).unwrap();
        assert_eq!(exact["subsets_examined"], 512);
        assert_eq!(exact["complete"], true);
        let heuristic = run(&args("sample 3 20 2 42")).unwrap();
        assert!(heuristic.get("complete").is_none());
        assert_eq!(heuristic["observations"].as_array().unwrap().len(), 2);
        assert!(run(&args("sample 17 0 1 42")).is_err());
        assert!(run(&args("enumerate 5")).is_err());
    }

    #[test]
    fn claims_are_recomputed_and_falsified_with_exact_integer_arithmetic() {
        let o = sample(4, 10, 123, None).unwrap();
        let mut corpus = json!({"observations": [o]});
        let ledger: Claim = serde_json::from_value(json!({"constant": 0,
            "coefficients": {"f":3,"r":1,"b":1,"c":1,"vertices":-1,"n":-4}}))
        .unwrap();
        assert_eq!(check_claim(&corpus, &ledger).unwrap()["minimum_slack"], "0");
        let false_claim = Claim {
            constant: -1,
            coefficients: BTreeMap::new(),
        };
        assert_eq!(
            check_claim(&corpus, &false_claim).unwrap()["falsified"],
            true
        );
        let unknown = Claim {
            constant: 0,
            coefficients: BTreeMap::from([("not_a_feature".into(), 1)]),
        };
        assert!(check_claim(&corpus, &unknown).is_err());
        corpus["observations"][0]["features"]["f"] = json!(999);
        assert!(check_claim(&corpus, &ledger).is_err());
        assert!(check_claim(&json!({"observations": []}), &ledger).is_err());
    }

    #[test]
    fn comparison_exports_replayable_near_run_best_boards_and_cutoffs() {
        let args = |s: &str| s.split_whitespace().map(String::from).collect::<Vec<_>>();
        let corpus = run(&args("compare 4 20 2 42 0")).unwrap();
        assert_eq!(corpus["variants"].as_array().unwrap().len(), 2);
        assert_eq!(
            corpus["variants"][1]["runs"][0]["stats"]["repair_successes"],
            0
        );
        assert!(
            corpus["variants"][1]["runs"][0]["stats"]["repair_cutoffs"]
                .as_u64()
                .unwrap()
                > 0
        );
        let zero = Claim {
            constant: 0,
            coefficients: BTreeMap::new(),
        };
        assert_eq!(check_claim(&corpus, &zero).unwrap()["minimum_slack"], "0");
        assert_eq!(
            summarize(&corpus).unwrap()["variants"]
                .as_array()
                .unwrap()
                .len(),
            2
        );
        assert!(run(&args("compare 17 0 1 1 1")).is_err());
    }
}
