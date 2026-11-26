//! Development and frozen sampler trials for the boundary-shuffle operator.
use anyhow::{anyhow, bail, Result};
use grid_graphs::boundary_shuffle::{probe, Status};
use grid_graphs::certificate_corpus::{
    observe, sample_timed, sample_timed_with_shuffle, Board, Observation,
};
use grid_graphs::neutral_search::{replay, Report};
use grid_graphs::shuffle_study_data::Manifest;
use serde::Serialize;
use serde_json::{json, Value};
use std::{
    collections::{BTreeMap, BTreeSet},
    env, fs,
    io::Write,
    path::Path,
    time::Instant,
};

fn save(path: &Path, value: &impl Serialize) -> Result<()> {
    let mut file = fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)?;
    serde_json::to_writer_pretty(&mut file, value)?;
    writeln!(file)?;
    Ok(())
}
fn load(path: &Path) -> Result<Board> {
    Board::parse(&fs::read_to_string(path)?).map_err(|e| anyhow!(e))
}
fn save_text(path: &Path, rows: &[String]) -> Result<()> {
    let mut f = fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)?;
    writeln!(f, "{}", rows.join("\n"))?;
    Ok(())
}
fn execute_case(m: &Manifest, index: usize, out: &Path) -> Result<Value> {
    m.validate().map_err(|e| anyhow!(e))?;
    if !out.is_dir() {
        bail!("output directory must exist");
    }
    let b = m.board(index).map_err(|e| anyhow!(e))?;
    let prefix = format!("case_{index:02}");
    for suffix in [
        "summary.json",
        "baseline.json",
        "baseline.txt",
        "operator.json",
        "operator.txt",
        "gain.json",
    ] {
        if out.join(format!("{prefix}.{suffix}")).exists() {
            bail!("case output already exists");
        }
    }
    let seed = 910_000_000 + 1000 * index as u64;
    let mut arms = Vec::new();
    // Balance order WITHIN each starting family, not just across all cases.
    for operator in if (index / 2) % 2 == 0 {
        [false, true]
    } else {
        [true, false]
    } {
        let start = Instant::now();
        let result = if operator {
            sample_timed_with_shuffle(&b, seed, 10_000, 77, m.policy.clone())
        } else {
            sample_timed(&b, seed, 10_000, 77)
        }
        .map_err(|e| anyhow!(e))?;
        let wall = start.elapsed().as_secs_f64();
        let name = if operator { "operator" } else { "baseline" };
        save_text(&out.join(format!("{prefix}.{name}.txt")), &result.best.rows)?;
        if !result.shuffle_gains.is_empty() {
            if !operator || result.shuffle_gains.len() != 1 {
                bail!("unexpected gain attribution for the score-76 trial");
            }
            let gain = &result.shuffle_gains[0];
            let source = Board::parse(&gain.before.rows.join("\n")).map_err(|e| anyhow!(e))?;
            replay(&source, &gain.trace, true).map_err(|e| anyhow!(e))?;
            save(
                &out.join(format!("{prefix}.gain.json")),
                &json!({"schema":"grid-graphs.boundary-shuffle-gain.v1","gain":gain}),
            )?;
        }
        arms.push(json!({"method":if operator {"random_plus_shuffle_v1"}else{"random_v1"},
            "success":result.best.features["f"]>=77,"best_f":result.best.features["f"],
            "first_target_seconds":result.stats.first_target_seconds,"first_target_method":result.stats.first_target_method,
            "wall_seconds":wall,"iterations":result.stats.iterations_completed,"stop_reason":result.stats.stop_reason,
            "shuffle_calls":result.stats.shuffle_calls,"shuffle_seconds":result.stats.shuffle_seconds,
            "shuffle_successes":result.stats.shuffle_successes,"shuffle_cutoffs":result.stats.shuffle_cutoffs,
            "shuffle_tests":result.stats.shuffle_tests,"shuffle_unchanged_skips":result.stats.shuffle_unchanged_skips}));
        save(
            &out.join(format!("{prefix}.{name}.json")),
            &json!({"schema":"grid-graphs.shuffle-sampler-trial.v1",
            "initial_rows":b.rows(),"seed":seed,"target_f":77,"time_budget_ms":10000,
            "policy":operator.then_some(&m.policy),"result":result}),
        )?;
    }
    let source = &m.candidates[m.inputs[index].source_id];
    let summary = json!({"schema":"grid-graphs.shuffle-heldout-case.v1","id":index,"source_id":source.source_id,
        "source_seed":source.source_seed,"source_family":source.family,"benchmark_seed":seed,"target_f":77,
        "time_budget_ms_per_method":10000,"method_order":"serial, balanced within each starting family",
        "arms":arms});
    save(&out.join(format!("{prefix}.summary.json")), &summary)?;
    Ok(summary)
}
fn development(out: &Path) -> Result<Value> {
    if !out.is_dir() {
        bail!("output directory must exist");
    }
    let mut states = Vec::new();
    let mut seen = BTreeSet::new();
    for (label, path) in [
        ("training", "data/neutral_escape_14.json"),
        (
            "previous_case06",
            "data/neutral_study_14/case_06.escape.json",
        ),
    ] {
        let r: Report = serde_json::from_str(&fs::read_to_string(path)?)?;
        let b = Board::parse(&r.original.rows.join("\n")).map_err(|e| anyhow!(e))?;
        replay(&b, &r.trace, true).map_err(|e| anyhow!(e))?;
        for (i, rows) in std::iter::once(&r.original.rows)
            .chain(r.trace[..r.trace.len() - 1].iter().map(|s| &s.rows))
            .enumerate()
        {
            let b = Board::parse(&rows.join("\n")).map_err(|e| anyhow!(e))?;
            if seen.insert(b.preserved.clone()) {
                states.push((format!("{label}_{i:02}"), b));
            }
        }
    }
    for i in 0..8 {
        let b = load(Path::new(&format!(
            "data/neutral_study_14/input_{i:02}.txt"
        )))?;
        if seen.insert(b.preserved.clone()) {
            states.push((format!("previous_input_{i:02}"), b));
        }
    }
    let mut records = Vec::new();
    let mut shuffle_hits = 0;
    let mut general_hits = 0;
    let mut fast_times = Vec::new();
    let mut general_times = Vec::new();
    let mut core_cycles = BTreeMap::<usize, usize>::new();
    let mut boundary_cycles = BTreeMap::<usize, usize>::new();
    for (i, (label, b)) in states.iter().enumerate() {
        let fast = probe(b, 100_000, 1000, false).map_err(|e| anyhow!(e))?;
        let fast_status = fast.status;
        let fast_seconds = fast.stats.elapsed_seconds;
        let diagnostic = probe(b, 100_000, 10_000, true).map_err(|e| anyhow!(e))?;
        for (&length, &count) in &diagnostic.stats.diagnostic_core_cycle_lengths {
            *core_cycles.entry(length).or_default() += count;
        }
        for (&length, &count) in &diagnostic.stats.diagnostic_boundary_cycle_lengths {
            *boundary_cycles.entry(length).or_default() += count;
        }
        if fast.status != diagnostic.status {
            bail!("diagnostic mismatch");
        }
        save(&out.join(format!("dev_{i:02}.probe.json")), &diagnostic)?;
        let start = Instant::now();
        let general =
            grid_graphs::deletion_search::search(b, 2, 500_000, 250).map_err(|e| anyhow!(e))?;
        let general_seconds = start.elapsed().as_secs_f64();
        fast_times.push(fast_seconds);
        general_times.push(general_seconds);
        let general_found = general.witness.is_some();
        shuffle_hits += usize::from(fast_status == Status::Found);
        general_hits += usize::from(general_found);
        if fast_status == Status::Found
            && general.status == grid_graphs::deletion_search::Status::ExhaustedNeighborhood
        {
            bail!("specialized gain contradicts completed general probe");
        }
        save(&out.join(format!("dev_{i:02}.general.json")), &general)?;
        records.push(json!({"id":i,"label":label,"rows":b.rows(),"f":observe(b).map_err(|e|anyhow!(e))?.features["f"],
            "shuffle_status":fast_status,"shuffle_seconds":fast_seconds,"shuffle_stats":fast.stats,
            "general_status":general.status,"general_seconds":general_seconds,"general_nodes":general.nodes,
            "general_found":general_found}));
    }
    fast_times.sort_by(f64::total_cmp);
    general_times.sort_by(f64::total_cmp);
    let median_fast = fast_times[fast_times.len() / 2];
    let median_general = general_times[general_times.len() / 2];
    let summary = json!({"schema":"grid-graphs.shuffle-development.v1",
        "scope":"previously examined states, development only; single timed probes, not held-out evidence",
        "states":records.len(),"shuffle_hits":shuffle_hits,"general_hits":general_hits,
        "median_shuffle_seconds":median_fast,"median_general_seconds":median_general,
        "reported_core_cycle_lengths":core_cycles,"reported_boundary_cycle_lengths":boundary_cycles,"records":records});
    save(&out.join("development.json"), &summary)?;
    Ok(
        json!({"states":states.len(),"shuffle_hits":shuffle_hits,"general_hits":general_hits,
        "median_shuffle_seconds":median_fast,"median_general_seconds":median_general,
        "reported_core_cycle_lengths":core_cycles,"reported_boundary_cycle_lengths":boundary_cycles,
        "artifact":out.join("development.json")}),
    )
}
fn run(args: &[String]) -> Result<Value> {
    if args.len() == 2 && args[0] == "archive-coverage" {
        let out = Path::new(&args[1]);
        let m: Manifest = serde_json::from_str(&fs::read_to_string(out.join("selection.json"))?)?;
        m.validate().map_err(|e| anyhow!(e))?;
        let mut unique = BTreeMap::<Vec<String>, Board>::new();
        for i in 0..8 {
            for name in ["baseline", "operator"] {
                let value: Value = serde_json::from_str(&fs::read_to_string(
                    out.join(format!("case_{i:02}.{name}.json")),
                )?)?;
                let values = value["result"]["near_optimal"]
                    .as_array()
                    .ok_or_else(|| anyhow!("missing archive"))?;
                for v in values
                    .iter()
                    .chain(std::iter::once(&value["result"]["best"]))
                {
                    let o: Observation = serde_json::from_value(v.clone())?;
                    let b = Board::parse(&o.rows.join("\n")).map_err(|e| anyhow!(e))?;
                    let actual = observe(&b).map_err(|e| anyhow!(e))?;
                    if actual.features != o.features || actual.local_3x3 != o.local_3x3 {
                        bail!("archive metadata mismatch");
                    }
                    if actual.features["f"] == 76 {
                        unique.insert(o.rows, b);
                    }
                }
            }
        }
        let (mut hits, mut contacts, mut geometric, mut cores, mut boundary_tests) =
            (0, 0, 0, 0, 0);
        let mut core_cycles = BTreeMap::<usize, usize>::new();
        let mut boundary_cycles = BTreeMap::<usize, usize>::new();
        let mut records = Vec::new();
        for (rows, b) in unique {
            let p = probe(&b, 100_000, 10_000, true).map_err(|e| anyhow!(e))?;
            if !matches!(p.status, Status::Found | Status::ExhaustedCandidates) {
                bail!("archive probe incomplete");
            }
            hits += usize::from(p.status == Status::Found);
            contacts += p.stats.contacts;
            geometric += p.stats.geometric_candidates;
            cores += p.stats.feasible_cores;
            boundary_tests += p.stats.boundary_tests;
            for (&k, &v) in &p.stats.diagnostic_core_cycle_lengths {
                *core_cycles.entry(k).or_default() += v;
            }
            for (&k, &v) in &p.stats.diagnostic_boundary_cycle_lengths {
                *boundary_cycles.entry(k).or_default() += v;
            }
            records.push(json!({"rows":rows,"probe":p}));
        }
        let result = json!({"schema":"grid-graphs.shuffle-posthoc-coverage.v1",
            "scope":"post-hoc inspection of saved score-76 snapshots; not all visited states and excluded from paired benchmark outcomes",
            "unique_states":records.len(),"gains":hits,"contacts":contacts,"geometric_candidates":geometric,
            "feasible_cores":cores,"boundary_tests":boundary_tests,"core_cycle_lengths":core_cycles,
            "boundary_cycle_lengths":boundary_cycles,"records":records});
        save(&out.join("posthoc_archive_coverage.json"), &result)?;
        return Ok(
            json!({"unique_states":records.len(),"gains":hits,"contacts":contacts,"geometric_candidates":geometric,
            "feasible_cores":cores,"boundary_tests":boundary_tests,"core_cycle_lengths":core_cycles,
            "boundary_cycle_lengths":boundary_cycles,"scope":"post-hoc; benchmark outcomes unchanged"}),
        );
    }
    if args.len() == 2 && args[0] == "summarize" {
        let out = Path::new(&args[1]);
        let m: Manifest = serde_json::from_str(&fs::read_to_string(out.join("selection.json"))?)?;
        m.validate().map_err(|e| anyhow!(e))?;
        let mut cells = [0usize; 4];
        let mut records = Vec::new();
        let (mut calls, mut hits, mut cutoffs, mut tests, mut cores, mut boundary_tests) =
            (0u64, 0u64, 0u64, 0u64, 0u64, 0u64);
        let mut seconds = 0.0;
        for i in 0..8 {
            let record: Value = serde_json::from_str(&fs::read_to_string(
                out.join(format!("case_{i:02}.summary.json")),
            )?)?;
            if record["schema"] != "grid-graphs.shuffle-heldout-case.v1" || record["id"] != i {
                bail!("wrong case record");
            }
            let mut results = Vec::new();
            let mut success = [false; 2];
            for (j, name) in ["baseline", "operator"].iter().enumerate() {
                let v: Value = serde_json::from_str(&fs::read_to_string(
                    out.join(format!("case_{i:02}.{name}.json")),
                )?)?;
                if v["initial_rows"] != json!(m.board(i).map_err(|e| anyhow!(e))?.rows())
                    || v["time_budget_ms"] != 10000
                {
                    bail!("trial setup mismatch");
                }
                let o: Observation = serde_json::from_value(v["result"]["best"].clone())?;
                let b = load(&out.join(format!("case_{i:02}.{name}.txt")))?;
                let actual = observe(&b).map_err(|e| anyhow!(e))?;
                if actual.rows != o.rows
                    || actual.features != o.features
                    || actual.local_3x3 != o.local_3x3
                {
                    bail!("witness mismatch");
                }
                success[j] = actual.features["f"] >= 77;
                results.push(v);
            }
            let stats = &results[1]["result"]["stats"];
            calls += stats["shuffle_calls"]
                .as_u64()
                .ok_or_else(|| anyhow!("counter missing"))?;
            hits += stats["shuffle_successes"]
                .as_u64()
                .ok_or_else(|| anyhow!("counter missing"))?;
            cutoffs += stats["shuffle_cutoffs"]
                .as_u64()
                .ok_or_else(|| anyhow!("counter missing"))?;
            tests += stats["shuffle_tests"]
                .as_u64()
                .ok_or_else(|| anyhow!("counter missing"))?;
            cores += stats["shuffle_feasible_cores"]
                .as_u64()
                .ok_or_else(|| anyhow!("counter missing"))?;
            boundary_tests += stats["shuffle_boundary_tests"]
                .as_u64()
                .ok_or_else(|| anyhow!("counter missing"))?;
            seconds += stats["shuffle_seconds"]
                .as_f64()
                .ok_or_else(|| anyhow!("time missing"))?;
            let coupled = success[0]
                && success[1]
                && stats["first_target_method"] == "random"
                && results[0]["result"]["stats"]["first_target_method"] == "random";
            if coupled
                && (results[0]["result"]["best"]["rows"] != results[1]["result"]["best"]["rows"]
                    || results[0]["result"]["stats"]["iterations_completed"]
                        != stats["iterations_completed"])
            {
                bail!("paired random trajectories diverged");
            }
            cells[usize::from(success[0]) + 2 * usize::from(success[1])] += 1;
            records.push(json!({"case":record,"paired_random_target_identical":coupled}));
        }
        let summary = json!({"schema":"grid-graphs.shuffle-heldout-summary.v1","inputs":8,
            "baseline_successes":cells[1]+cells[3],"operator_variant_successes":cells[2]+cells[3],
            "baseline_only":cells[1],"operator_only":cells[2],"both":cells[3],"neither":cells[0],
            "shuffle_calls":calls,"shuffle_gains":hits,"shuffle_cutoffs":cutoffs,"shuffle_tests":tests,
            "shuffle_seconds":seconds,"shuffle_feasible_cores":cores,"shuffle_boundary_tests":boundary_tests,
            "scope":"frozen paired ten-second trials; descriptive outcomes, not a significance or universal performance claim","records":records});
        save(&out.join("summary.json"), &summary)?;
        return Ok(summary);
    }
    if args.len() == 3 && args[0] == "select" {
        let out = Path::new(&args[2]);
        if !out.is_dir() {
            bail!("output directory must exist");
        }
        if out.join("selection.json").exists() {
            bail!("selection already frozen");
        }
        let m =
            grid_graphs::shuffle_study_data::select(Path::new(&args[1])).map_err(|e| anyhow!(e))?;
        save(&out.join("selection.json"), &m)?;
        for input in &m.inputs {
            save_text(
                &out.join(format!("input_{:02}.txt", input.id)),
                &m.candidates[input.source_id].rows,
            )?;
        }
        return Ok(
            json!({"manifest":out.join("selection.json"),"excluded_symmetry_classes":m.excluded_rows.len(),
            "inputs":m.inputs,"candidate_scores":m.candidates.iter().map(|c|c.observed_f).collect::<Vec<_>>(),"policy":m.policy}),
        );
    }
    if args.len() == 4 && args[0] == "case" {
        let m: Manifest = serde_json::from_str(&fs::read_to_string(&args[1])?)?;
        return execute_case(&m, args[2].parse()?, Path::new(&args[3]));
    }
    if args.len() == 6 && args[0] == "sample" {
        let b = load(Path::new(&args[1]))?;
        let seed = args[2].parse()?;
        let ms = args[3].parse()?;
        let target = args[4].parse()?;
        if ms > 60_000 {
            bail!("sample time must be at most 60000 ms");
        }
        let result = match args[5].as_str() {
            "baseline" => sample_timed(&b, seed, ms, target),
            "operator" => sample_timed_with_shuffle(&b, seed, ms, target, Default::default()),
            _ => bail!("expected baseline or operator"),
        }
        .map_err(|e| anyhow!(e))?;
        return Ok(
            json!({"schema":"grid-graphs.shuffle-sample.v1","initial_rows":b.rows(),"seed":seed,
            "time_budget_ms":ms,"target_f":target,"method":args[5],"result":result}),
        );
    }
    if args.len() == 2 && args[0] == "development" {
        return development(Path::new(&args[1]));
    }
    if (args.len() == 4 || args.len() == 5) && args[0] == "probe" {
        let diagnostics = args.get(4).is_some_and(|x| x == "diagnostics");
        if args.len() == 5 && !diagnostics {
            bail!("expected diagnostics");
        }
        return Ok(serde_json::to_value(
            probe(
                &load(Path::new(&args[1]))?,
                args[2].parse()?,
                args[3].parse()?,
                diagnostics,
            )
            .map_err(|e| anyhow!(e))?,
        )?);
    }
    bail!("usage: shuffle_study probe U_WITNESS MAX_TESTS MAX_MS [diagnostics]\n       shuffle_study development OUTPUT_DIRECTORY\n       shuffle_study select PRIOR_STUDY_DIRECTORY OUTPUT_DIRECTORY\n       shuffle_study case MANIFEST INDEX OUTPUT_DIRECTORY\n       shuffle_study summarize OUTPUT_DIRECTORY\n       shuffle_study archive-coverage OUTPUT_DIRECTORY\n       shuffle_study sample U_WITNESS SEED MAX_MS TARGET baseline|operator")
}
fn main() -> Result<()> {
    println!(
        "{}",
        serde_json::to_string_pretty(&run(&env::args().skip(1).collect::<Vec<_>>())?)?
    );
    Ok(())
}
