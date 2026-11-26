//! Search and independently replay bounded neutral escape traces.
use anyhow::{anyhow, bail, Result};
use grid_graphs::certificate_corpus::{Board, Observation};
use grid_graphs::neutral_search::{search, Config, Report, TraceStep};
use serde_json::{json, Value};
use std::{
    env, fs,
    io::{self, Write},
};

// Separate graph reconstruction: enumerate primal edges, union their endpoints,
// and reject a cycle. This does not use the search's star-insertion DSU or BFS.
fn checked_score(b: &Board) -> Result<usize> {
    let mut parent: Vec<_> = (0..b.n * b.n).collect();
    fn root(parent: &mut [usize], mut v: usize) -> usize {
        while parent[v] != v {
            parent[v] = parent[parent[v]];
            v = parent[v];
        }
        v
    }
    for y in 0..b.n {
        for x in 0..b.n {
            let v = y * b.n + x;
            for w in [
                (x + 1 < b.n).then_some(v + 1),
                (y + 1 < b.n).then_some(v + b.n),
            ]
            .into_iter()
            .flatten()
            {
                if !(b.preserved[v] || b.preserved[w]) {
                    continue;
                }
                let a = root(&mut parent, v);
                let c = root(&mut parent, w);
                if a == c {
                    bail!("trace contains a forced cycle");
                }
                parent[a] = c;
            }
        }
    }
    Ok(b.preserved.iter().filter(|&&f| f).count())
}
fn audit(report: &Report) -> Result<Value> {
    if report.schema != "grid-graphs.neutral-plateau.v1" {
        bail!("unsupported trace schema");
    }
    let escape = report.status == "escape_found";
    if report.trace_kind
        != if escape {
            "escape"
        } else {
            "neutral_representative"
        }
    {
        bail!("trace kind mismatch");
    }
    audit_trace(
        &report.original,
        &report.trace,
        &report.endpoint,
        escape,
        report.config.mixed,
    )
}
fn audit_trace(
    input: &Observation,
    trace: &[TraceStep],
    endpoint: &Observation,
    escape: bool,
    mixed: bool,
) -> Result<Value> {
    let original = Board::parse(&input.rows.join("\n")).map_err(|e| anyhow!(e))?;
    if original.n > 15 {
        bail!("unexpected trace dimensions");
    }
    let mut b = original.clone();
    let initial = checked_score(&b)?;
    if input.features.get("f").copied() != Some(initial as i64) {
        bail!("initial score mismatch");
    }
    if escape && trace.is_empty() {
        bail!("missing escape trace");
    }
    let mut scores = vec![initial];
    for (index, step) in trace.iter().enumerate() {
        let mut touched = vec![false; b.n * b.n];
        for &v in &step.exchange.deleted {
            if v >= touched.len() || touched[v] || !b.preserved[v] {
                bail!("invalid deletion");
            }
            touched[v] = true;
        }
        for &v in &step.exchange.added {
            if v >= touched.len() || touched[v] || b.preserved[v] {
                bail!("invalid addition");
            }
            touched[v] = true;
        }
        let gain = escape && index + 1 == trace.len();
        let d = step.exchange.deleted.len();
        let a = step.exchange.added.len();
        if gain {
            if d > 2 || a != d + 1 {
                bail!("invalid gain cardinality");
            }
        } else if !(1..=2).contains(&d) || a != d || (!mixed && d == 2) {
            bail!("invalid neutral cardinality");
        }
        for &v in &step.exchange.deleted {
            b.preserved[v] = false;
        }
        for &v in &step.exchange.added {
            b.preserved[v] = true;
        }
        let score = checked_score(&b)?;
        let missing = original
            .preserved
            .iter()
            .zip(&b.preserved)
            .filter(|(a, c)| **a && !**c)
            .count();
        if score != initial + usize::from(gain)
            || step.f != score as i64
            || step.rows != b.rows()
            || step.missing_original_f != missing
        {
            bail!("trace snapshot mismatch");
        }
        scores.push(score);
    }
    if endpoint.rows != b.rows()
        || endpoint.features.get("f").copied() != Some(checked_score(&b)? as i64)
    {
        bail!("endpoint mismatch");
    }
    Ok(
        json!({"schema":"grid-graphs.neutral-trace-audit.v1","accepted":true,
        "scope":"literal forced-edge replay of this trace; not search coverage or shortest-path validation",
        "escape":escape,"steps_checked":trace.len(),"scores":scores,
        "missing_original_f":original.preserved.iter().zip(&b.preserved).filter(|(a,c)|**a && !**c).count()}),
    )
}
fn audit_shuffle(g: &grid_graphs::boundary_shuffle::Gain) -> Result<Value> {
    let b = Board::parse(&g.before.rows.join("\n")).map_err(|e| anyhow!(e))?;
    if g.trace.len() != 2
        || g.trace[0].exchange.deleted != g.core.deleted
        || g.trace[0].exchange.added != g.core.added
        || g.trace[1].exchange.added != vec![g.boundary]
        || !g.trace[1].exchange.deleted.is_empty()
    {
        bail!("shuffle metadata/trace mismatch");
    }
    let is_boundary =
        |v: usize| v % b.n == 0 || v % b.n + 1 == b.n || v / b.n == 0 || v / b.n + 1 == b.n;
    if g.boundary >= b.preserved.len()
        || !is_boundary(g.boundary)
        || g.core
            .deleted
            .iter()
            .chain(&g.core.added)
            .any(|&v| v >= b.preserved.len() || is_boundary(v))
    {
        bail!("shuffle boundary/interior mismatch");
    }
    let [a, c] = g.core.deleted;
    let (ax, ay) = ((a % b.n) as isize, (a / b.n) as isize);
    let (cx, cy) = ((c % b.n) as isize, (c / b.n) as isize);
    if (ax - cx).abs() + (ay - cy).abs() != 2 || (ax != cx && ay != cy) {
        bail!("not an opposite contact pair");
    }
    let (mx, my) = ((ax + cx) / 2, (ay + cy) / 2);
    let center = my as usize * b.n + mx as usize;
    if g.core.center != center || b.preserved[center] {
        bail!("invalid shuffle center");
    }
    let (dx, dy) = ((cx - ax) / 2, (cy - ay) / 2);
    let (px, py) = (-dy, dx);
    let coords = |v: usize| {
        let (x, y) = ((v % b.n) as isize - mx, (v / b.n) as isize - my);
        (x * dx + y * dy, x * px + y * py)
    };
    let s = coords(g.core.added[0]);
    let t = coords(g.core.added[1]);
    let pattern = |s: (isize, isize), t: (isize, isize)| {
        s.0 == 0 && s.1.abs() == 1 && t.0.abs() == 2 && t.1 == -s.1
    };
    if !pattern(s, t) && !pattern(t, s) {
        bail!("invalid shuffle geometry");
    }
    audit_trace(&g.before, &g.trace, &g.after, true, true)
}
fn run(args: &[String]) -> Result<Value> {
    if args.len() >= 2 && args[0] == "check-witness" {
        let mut records = Vec::new();
        for path in &args[1..] {
            let b = Board::parse(&fs::read_to_string(path)?).map_err(|e| anyhow!(e))?;
            records.push(json!({"path":path,"n":b.n,"f":checked_score(&b)?,"accepted":true}));
        }
        return Ok(
            json!({"schema":"grid-graphs.independent-board-batch-audit.v1","records":records}),
        );
    }
    if args.len() == 2 && args[0] == "reproduce" {
        let prior: Report = serde_json::from_str(&fs::read_to_string(&args[1])?)?;
        let b = Board::parse(&prior.original.rows.join("\n")).map_err(|e| anyhow!(e))?;
        let report = search(&b, prior.config).map_err(|e| anyhow!(e))?;
        audit(&report)?;
        return Ok(serde_json::to_value(report)?);
    }
    if args.len() == 3 && args[0] == "archive" {
        let raw = fs::read_to_string(&args[1])?;
        let report: Report = serde_json::from_str(&raw)?;
        let verified = audit(&report)?;
        if report.status != "escape_found" {
            bail!("archive requires an escape trace");
        }
        let paths = [
            format!("{}.json", args[2]),
            format!("{}.txt", args[2]),
            format!("{}.audit.json", args[2]),
        ];
        if paths.iter().any(|p| std::path::Path::new(p).exists()) {
            bail!("refusing to overwrite an existing archive");
        }
        let contents = [
            raw,
            format!(
                "# Verified neutral escape: {} -> {}. U=hole; .=preserved.\n{}\n",
                report.original.features["f"],
                report.endpoint.features["f"],
                report.endpoint.rows.join("\n")
            ),
            serde_json::to_string_pretty(&verified)? + "\n",
        ];
        for (path, content) in paths.iter().zip(contents) {
            let mut file = fs::OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(path)?;
            file.write_all(content.as_bytes())?;
        }
        return Ok(
            json!({"schema":"grid-graphs.neutral-archive.v1", "paths":paths,
            "steps":report.trace.len(), "final_f":report.endpoint.features["f"]}),
        );
    }
    if args.len() == 2 && args[0] == "verify" {
        let value: Value = serde_json::from_str(&fs::read_to_string(&args[1])?)?;
        if value["schema"] == "grid-graphs.boundary-shuffle-gain.v1" {
            let gain: grid_graphs::boundary_shuffle::Gain =
                serde_json::from_value(value["gain"].clone())?;
            return audit_shuffle(&gain);
        }
        if value["schema"] == "grid-graphs.boundary-shuffle-probe.v1" {
            let p: grid_graphs::boundary_shuffle::Probe = serde_json::from_value(value)?;
            let gain = p
                .gain
                .ok_or_else(|| anyhow!("probe has no gain to replay"))?;
            return audit_shuffle(&gain);
        }
        if value["schema"] == "grid-graphs.neutral-simplification.v1" {
            let s: grid_graphs::trace_simplify::Simplification = serde_json::from_value(value)?;
            return audit_trace(&s.original, &s.trace, &s.endpoint, true, s.mixed);
        }
        return audit(&serde_json::from_value(value)?);
    }
    if args.len() != 3 && args.len() != 8 {
        bail!("usage: neutral_plateau U_WITNESS one|mixed SEED [TIME_MS NODE_LIMIT STATE_LIMIT BEAM_WIDTH MAX_DEPTH]\n       neutral_plateau verify REPORT_JSON\n       neutral_plateau reproduce REPORT_JSON\n       neutral_plateau archive REPORT_JSON OUTPUT_STEM");
    }
    let b = Board::parse(&fs::read_to_string(&args[0])?).map_err(|e| anyhow!(e))?;
    let mixed = match args[1].as_str() {
        "one" => false,
        "mixed" => true,
        _ => bail!("phase must be one or mixed"),
    };
    let mut cfg = Config {
        mixed,
        seed: args[2].parse()?,
        ..Config::default()
    };
    if args.len() == 8 {
        cfg.time_limit_ms = args[3].parse()?;
        cfg.node_limit = args[4].parse()?;
        cfg.state_limit = args[5].parse()?;
        cfg.beam_width = args[6].parse()?;
        cfg.max_depth = args[7].parse()?;
    }
    let report = search(&b, cfg).map_err(|e| anyhow!(e))?;
    audit(&report)?;
    Ok(serde_json::to_value(report)?)
}
fn main() -> Result<()> {
    let output = run(&env::args().skip(1).collect::<Vec<_>>())?;
    let mut out = io::BufWriter::new(io::stdout().lock());
    serde_json::to_writer_pretty(&mut out, &output)?;
    writeln!(out)?;
    Ok(())
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn shuffle_audit_checks_geometry_metadata_and_forced_edges() {
        let p: grid_graphs::boundary_shuffle::Probe = serde_json::from_str(include_str!(
            "../../data/shuffle_development_14/dev_11.probe.json"
        ))
        .unwrap();
        let mut gain = p.gain.unwrap();
        audit_shuffle(&gain).unwrap();
        gain.core.center += 1;
        assert!(audit_shuffle(&gain).is_err());
    }
    #[test]
    fn independent_checker_agrees_on_all_four_square_subsets() {
        for mask in 0u32..1 << 16 {
            let b = Board {
                n: 4,
                preserved: (0..16).map(|v| mask & (1 << v) != 0).collect(),
            };
            assert_eq!(
                checked_score(&b).is_ok(),
                grid_graphs::certificate_corpus::observe(&b).is_ok()
            );
        }
    }
    #[test]
    fn trace_audit_accepts_valid_and_rejects_corrupted_moves() {
        let b = Board::parse("UU\nUU").unwrap();
        let mut r = search(&b, Config::default()).unwrap();
        assert_eq!(audit(&r).unwrap()["accepted"], true);
        r.trace[0].rows = vec!["..".into(), "..".into()];
        assert!(audit(&r).is_err());
    }

    #[test]
    fn archived_escape_passes_independent_forced_edge_audit() {
        let report: Report =
            serde_json::from_str(include_str!("../../data/neutral_escape_14.json")).unwrap();
        let checked = audit(&report).unwrap();
        assert_eq!(checked["accepted"], true);
        assert_eq!(checked["steps_checked"], 12);
        assert_eq!(checked["missing_original_f"], 9);
    }

    #[test]
    fn simplified_trace_passes_independent_forced_edge_audit() {
        let s: grid_graphs::trace_simplify::Simplification = serde_json::from_str(include_str!(
            "../../data/neutral_escape_14_simplified_reordered.json"
        ))
        .unwrap();
        assert_eq!(
            audit_trace(&s.original, &s.trace, &s.endpoint, true, s.mixed).unwrap()["accepted"],
            true
        );
    }
}
