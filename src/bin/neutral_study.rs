//! Trace simplification and predeclared held-out experiments.
use anyhow::{anyhow, bail, Result};
use grid_graphs::certificate_corpus::{observe, sample_timed, Board};
use grid_graphs::holdout_study::{neutral_timed, Manifest};
use grid_graphs::neutral_search::Report;
use serde::Serialize;
use serde_json::{json, Value};
use std::{env, fs, io::Write, path::Path};

fn save(path: &Path, value: &impl Serialize) -> Result<()> {
    let mut file = fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)?;
    serde_json::to_writer_pretty(&mut file, value)?;
    writeln!(file)?;
    Ok(())
}
fn save_text(path: &Path, rows: &[String]) -> Result<()> {
    let mut file = fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)?;
    writeln!(file, "{}", rows.join("\n"))?;
    Ok(())
}
fn ensure_dir(path: &Path) -> Result<()> {
    if !path.is_dir() {
        bail!("output directory must already exist: {}", path.display());
    }
    Ok(())
}
fn execute_case(manifest: &Manifest, index: usize, out: &Path) -> Result<Value> {
    manifest.validate().map_err(|e| anyhow!(e))?;
    ensure_dir(out)?;
    let board = manifest.board(index).map_err(|e| anyhow!(e))?;
    let seed = 900_000_000 + 1000 * index as u64;
    let prefix = format!("case_{index:02}");
    for suffix in [
        "summary.json",
        "baseline.json",
        "baseline.txt",
        "neutral.json",
        "neutral.txt",
        "escape.json",
    ] {
        if out.join(format!("{prefix}.{suffix}")).exists() {
            bail!("case output already exists");
        }
    }
    let mut arms = Vec::new();
    for neutral in if index % 2 == 0 {
        [false, true]
    } else {
        [true, false]
    } {
        if neutral {
            let result = neutral_timed(&board, seed, 10_000, false).map_err(|e| anyhow!(e))?;
            save(&out.join(format!("{prefix}.neutral.json")), &result)?;
            let endpoint = result
                .attempts
                .last()
                .map(|r| r.endpoint.rows.clone())
                .unwrap_or_else(|| board.rows());
            save_text(&out.join(format!("{prefix}.neutral.txt")), &endpoint)?;
            if result.success {
                save(
                    &out.join(format!("{prefix}.escape.json")),
                    result.attempts.last().unwrap(),
                )?;
            }
            let work: u64 = result.attempts.iter().map(|r| r.stats.work_nodes).sum();
            let cutoffs: usize = result.attempts.iter().map(|r| r.stats.probe_cutoffs).sum();
            let discards: usize = result.attempts.iter().map(|r| r.stats.beam_discarded).sum();
            arms.push(json!({"method":"neutral_unpruned","success":result.success,
                "first_target_seconds":result.first_target_seconds,"wall_seconds":result.wall_seconds,
                "stop_reason":result.stop_reason,"attempts":result.attempts.len(),"work_nodes":work,
                "probe_cutoffs":cutoffs,"beam_discards":discards,
                "winning_trace_steps":result.success.then(||result.attempts.last().unwrap().trace.len()),
                "best_f":if result.success {77}else{76},"use_certified_radius":false}));
        } else {
            let started = std::time::Instant::now();
            let result = sample_timed(&board, seed, 10_000, 77).map_err(|e| anyhow!(e))?;
            let wall = started.elapsed().as_secs_f64();
            save_text(
                &out.join(format!("{prefix}.baseline.txt")),
                &result.best.rows,
            )?;
            arms.push(json!({"method":"random_v1","success":result.best.features["f"]>=77,
                "first_target_seconds":result.stats.first_target_seconds,"wall_seconds":wall,
                "stop_reason":result.stats.stop_reason,"iterations":result.stats.iterations_completed,
                "best_f":result.best.features["f"]}));
            save(
                &out.join(format!("{prefix}.baseline.json")),
                &json!({"schema":"grid-graphs.timed-baseline.v1",
                "seed":seed,"time_budget_ms":10000,"target_f":77,"best":result.best,"stats":result.stats}),
            )?;
        }
    }
    let source = &manifest.candidates[manifest.inputs[index].source_id];
    let result = json!({"schema":"grid-graphs.heldout-case.v1","id":index,"source_id":source.source_id,
        "source_family":source.family,"source_seed":source.source_seed,"benchmark_seed":seed,
        "n":14,"initial_f":76,"target_f":77,"time_budget_ms_per_method":10000,
        "method_order":"counterbalanced by case parity; serial execution",
        "scope":"one fixed run per method per selected input; descriptive, not population-level evidence",
        "arms":arms});
    save(&out.join(format!("{prefix}.summary.json")), &result)?;
    Ok(result)
}
fn run(args: &[String]) -> Result<Value> {
    if (args.len() == 4 || args.len() == 5) && args[0] == "posthoc-full-probes" {
        let manifest: Manifest = serde_json::from_str(&fs::read_to_string(&args[1])?)?;
        manifest.validate().map_err(|e| anyhow!(e))?;
        let index: usize = args[2].parse()?;
        let b = manifest.board(index).map_err(|e| anyhow!(e))?;
        let out = Path::new(&args[3]);
        ensure_dir(out)?;
        let mixed = if args.len() == 5 {
            if args[4] != "mixed" {
                bail!("expected mixed");
            }
            true
        } else {
            false
        };
        let report = grid_graphs::neutral_search::search(
            &b,
            grid_graphs::neutral_search::Config {
                seed: 900_000_000 + 1000 * index as u64,
                time_limit_ms: 10_000,
                use_certified_radius: false,
                larger_probe_stride: 1,
                mixed,
                ..Default::default()
            },
        )
        .map_err(|e| anyhow!(e))?;
        let path = out.join(format!(
            "posthoc_case_{index:02}_{}full_probes.json",
            if mixed { "mixed_" } else { "" }
        ));
        save(&path, &report)?;
        return Ok(
            json!({"scope":"post-hoc probe-coverage diagnostic; excluded from frozen benchmark counts",
            "path":path,"status":report.status,"best_f":report.endpoint.features["f"],"stats":report.stats}),
        );
    }
    if args.len() == 2 && args[0] == "summarize" {
        let out = Path::new(&args[1]);
        let manifest: Manifest =
            serde_json::from_str(&fs::read_to_string(out.join("selection.json"))?)?;
        manifest.validate().map_err(|e| anyhow!(e))?;
        let mut cases = Vec::new();
        let mut wins = [0usize; 4];
        for i in 0..8 {
            let input = manifest.board(i).map_err(|e| anyhow!(e))?;
            let obs = observe(&input).map_err(|e| anyhow!(e))?;
            let record: Value = serde_json::from_str(&fs::read_to_string(
                out.join(format!("case_{i:02}.summary.json")),
            )?)?;
            if record["id"] != i || record["time_budget_ms_per_method"] != 10000 {
                bail!("case metadata mismatch");
            }
            let mut success = [false; 2];
            for arm in record["arms"]
                .as_array()
                .ok_or_else(|| anyhow!("missing arms"))?
            {
                let (slot, name) = match arm["method"].as_str() {
                    Some("random_v1") => (0, "baseline"),
                    Some("neutral_unpruned") => (1, "neutral"),
                    _ => bail!("unexpected method"),
                };
                let board = Board::parse(&fs::read_to_string(
                    out.join(format!("case_{i:02}.{name}.txt")),
                )?)
                .map_err(|e| anyhow!(e))?;
                let verified = observe(&board).map_err(|e| anyhow!(e))?;
                success[slot] = verified.features["f"] >= 77;
                if arm["success"] != success[slot] || arm["best_f"] != verified.features["f"] {
                    bail!("result/witness mismatch");
                }
            }
            let neutral: Value = serde_json::from_str(&fs::read_to_string(
                out.join(format!("case_{i:02}.neutral.json")),
            )?)?;
            for attempt in neutral["attempts"]
                .as_array()
                .ok_or_else(|| anyhow!("missing attempts"))?
            {
                let r: Report = serde_json::from_value(attempt.clone())?;
                if r.config.use_certified_radius
                    || r.original_excluded_deletion_radius.is_some()
                    || r.original.rows != input.rows()
                {
                    bail!("neutral attempt used unexpected input or pruning");
                }
                grid_graphs::neutral_search::replay(&input, &r.trace, r.status == "escape_found")
                    .map_err(|e| anyhow!(e))?;
            }
            wins[usize::from(success[0]) + 2 * usize::from(success[1])] += 1;
            cases.push(json!({"id":i,"source_id":manifest.inputs[i].source_id,
                "shape":{"r":obs.features["r"],"b":obs.features["b"],"c":obs.features["c"],"z":obs.features["z"]},
                "arms":record["arms"]}));
        }
        let summary = json!({"schema":"grid-graphs.neutral-heldout-summary.v1","cases":cases,
            "inputs":8,"seconds_allowed_per_method_per_input":10,
            "baseline_successes":wins[1]+wins[3],"neutral_successes":wins[2]+wins[3],
            "baseline_only":wins[1],"neutral_only":wins[2],"both":wins[3],"neither":wins[0],
            "scope":"descriptive paired outcomes on the frozen diverse selection; no significance claim or inferred hybrid performance"});
        save(&out.join("summary.json"), &summary)?;
        return Ok(summary);
    }
    if args.len() == 2 && args[0] == "select" {
        let out = Path::new(&args[1]);
        ensure_dir(out)?;
        if out.join("selection.json").exists() {
            bail!("selection is already frozen");
        }
        let manifest = grid_graphs::holdout_study::select().map_err(|e| anyhow!(e))?;
        save(&out.join("selection.json"), &manifest)?;
        for input in &manifest.inputs {
            save_text(
                &out.join(format!("input_{:02}.txt", input.id)),
                &manifest.candidates[input.source_id].rows,
            )?;
        }
        return Ok(
            json!({"manifest":out.join("selection.json"),"inputs":manifest.inputs,
            "candidate_scores":manifest.candidates.iter().map(|c|c.observed_f).collect::<Vec<_>>()}),
        );
    }
    if args.len() == 4 && args[0] == "case" {
        let manifest: Manifest = serde_json::from_str(&fs::read_to_string(&args[1])?)?;
        return execute_case(&manifest, args[2].parse()?, Path::new(&args[3]));
    }
    if args.len() == 2 && args[0] == "control" {
        let out = Path::new(&args[1]);
        ensure_dir(out)?;
        let b =
            Board::parse(include_str!("../../data/corpus_trap_14.txt")).map_err(|e| anyhow!(e))?;
        let mut records = Vec::new();
        for use_bound in [false, true] {
            let name = if use_bound {
                "control_pruned"
            } else {
                "control_unpruned"
            };
            if out.join(format!("{name}.json")).exists() {
                bail!("control already exists");
            }
            let result = neutral_timed(&b, 20260908, 10_000, use_bound).map_err(|e| anyhow!(e))?;
            save(&out.join(format!("{name}.json")), &result)?;
            if result.success {
                save(
                    &out.join(format!("{name}.escape.json")),
                    result.attempts.last().unwrap(),
                )?;
            }
            records.push(json!({"use_certified_radius":use_bound,"success":result.success,
                "first_target_seconds":result.first_target_seconds,"wall_seconds":result.wall_seconds,
                "attempts":result.attempts.len(),"work_nodes":result.attempts.iter().map(|r|r.stats.work_nodes).sum::<u64>(),
                "probes_skipped_by_original_bound":result.attempts.iter().map(|r|r.stats.probes_skipped_by_original_bound).sum::<usize>(),
                "winning_trace":result.attempts.last().filter(|_|result.success).map(|r|r.trace.iter().map(|s|s.exchange.clone()).collect::<Vec<_>>())}));
        }
        let summary = json!({"schema":"grid-graphs.original-pruning-control.v1","seed":20260908,
            "time_budget_ms_per_arm":10000,"scope":"training-input control, excluded from held-out results","arms":records});
        save(&out.join("control.summary.json"), &summary)?;
        return Ok(summary);
    }
    if args.len() == 4 && args[0] == "simplify" {
        let source: Report = serde_json::from_str(&fs::read_to_string(&args[1])?)?;
        let ordered = match args[2].as_str() {
            "ordered" => true,
            "reorder" => false,
            _ => bail!("expected ordered or reorder"),
        };
        let result = grid_graphs::trace_simplify::simplify(&source, ordered, 100_000, 10_000)
            .map_err(|e| anyhow!(e))?;
        save(Path::new(&args[3]), &result)?;
        return Ok(
            json!({"path":args[3],"status":result.status,"minimum_proved":result.minimum_proved,
            "retained_source_indices":result.retained_source_indices,"states_examined":result.states_examined,
            "source_neutral_moves":result.source_neutral_moves}),
        );
    }
    bail!("usage: neutral_study simplify ESCAPE_JSON ordered|reorder OUTPUT_JSON\n       neutral_study select OUTPUT_DIRECTORY\n       neutral_study case MANIFEST INDEX OUTPUT_DIRECTORY\n       neutral_study control OUTPUT_DIRECTORY\n       neutral_study summarize OUTPUT_DIRECTORY\n       neutral_study posthoc-full-probes MANIFEST INDEX OUTPUT_DIRECTORY [mixed]")
}
fn main() -> Result<()> {
    let result = run(&env::args().skip(1).collect::<Vec<_>>())?;
    println!("{}", serde_json::to_string_pretty(&result)?);
    Ok(())
}
