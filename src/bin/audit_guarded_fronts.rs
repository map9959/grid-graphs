//! Independent literal-primal audit of the four guarded-front batch001 families.
use anyhow::{anyhow, bail, ensure, Context, Result};
use grid_graphs::certificate_corpus::{observe, Board, Observation};
use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;
use std::fs::{File, OpenOptions};
use std::io::{BufReader, BufWriter, Write};

#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct Ledger {
    f: i64,
    r: i64,
    b: i64,
    c: i64,
    z: i64,
}

impl Ledger {
    fn from_observation(o: &Observation) -> Self {
        Self {
            f: o.features["f"],
            r: o.features["r"],
            b: o.features["b"],
            c: o.features["c"],
            z: o.features["z"],
        }
    }

    fn difference(&self, before: &Self) -> Self {
        Self {
            f: self.f - before.f,
            r: self.r - before.r,
            b: self.b - before.b,
            c: self.c - before.c,
            z: self.z - before.z,
        }
    }
}

#[derive(Deserialize)]
struct Control {
    before_rows: Vec<String>,
    after_rows: Vec<String>,
    before: Ledger,
    after: Ledger,
    selected: Vec<usize>,
}

#[derive(Deserialize)]
struct Fixture {
    name: String,
    n: usize,
    base_rows: Vec<String>,
    levels: Vec<usize>,
    selected: Vec<usize>,
    patch: Vec<usize>,
    protected_u: Vec<usize>,
    optional: Vec<usize>,
    base_ledger: Ledger,
    deltas: Ledger,
    subsets: u64,
    feasible_masks: Vec<u64>,
    isolate_witnesses: Vec<usize>,
}

#[derive(Deserialize)]
struct Batch {
    schema: u32,
    all_rows_control: Control,
    fixtures: Vec<Fixture>,
}

#[derive(Serialize)]
struct FixtureSummary {
    name: String,
    n: usize,
    optional_variables: usize,
    masks_checked: u64,
    cyclic_masks: u64,
    feasible_masks: u64,
    exchanges_checked: u64,
    isolate_witness_checks: u64,
    base_ledger: Ledger,
    verified_delta: Ledger,
}

// Board::neighbors is crate-private; enumerate physical neighbours locally.
fn neighbors(n: usize, v: usize) -> impl Iterator<Item = usize> {
    let (x, y) = (v % n, v / n);
    [
        (x > 0).then(|| v - 1),
        (x + 1 < n).then(|| v + 1),
        (y > 0).then(|| v - n),
        (y + 1 < n).then(|| v + n),
    ]
    .into_iter()
    .flatten()
}

fn parse_rows(rows: &[String], n: usize) -> Result<Board> {
    ensure!((1..=15).contains(&n), "side must be in 1..=15");
    ensure!(
        rows.len() == n && rows.iter().all(|r| r.len() == n),
        "invalid rows"
    );
    let board = Board::parse(&rows.join("\n")).map_err(|e| anyhow!(e))?;
    ensure!(board.n == n && board.rows() == rows, "noncanonical rows");
    Ok(board)
}

fn checked_ledger(board: &Board) -> Result<Ledger> {
    observe(board)
        .map(|o| Ledger::from_observation(&o))
        .map_err(|e| anyhow!(e))
}

fn unique_indices(values: &[usize], bound: usize, what: &str) -> Result<()> {
    ensure!(values.iter().all(|&v| v < bound), "{what}: out of range");
    ensure!(
        values.iter().copied().collect::<BTreeSet<_>>().len() == values.len(),
        "{what}: duplicates"
    );
    Ok(())
}

fn rectangle(n: usize, x: usize, y: usize, w: usize, h: usize) -> Vec<usize> {
    (y..y + h)
        .flat_map(|yy| (x..x + w).map(move |xx| yy * n + xx))
        .collect()
}

// Freeze the batch's physical skeletons, independently of archived row strings.
fn skeleton(kind: &str) -> Board {
    let n = if kind == "rooted15" { 15 } else { 14 };
    let mut board = Board {
        n,
        preserved: vec![false; n * n],
    };
    for y in 0..n {
        for x in 0..n {
            board.preserved[y * n + x] = match kind {
                "rooted14" => {
                    (x == 3 && ((3..=10).contains(&y) || y <= 1))
                        || ([4, 7, 10].contains(&y) && (5..=10).contains(&x))
                        || (y == 0 && (5..=11).contains(&x))
                        || (x == 13 && y <= 10)
                }
                "rootless14" => {
                    ([4, 7, 10].contains(&y) && x <= 10) || (x == 13 && (3..=11).contains(&y))
                }
                "rooted15" => {
                    x == 1
                        || x == 14
                        || ([1, 4, 7, 10].contains(&y) && (3..=11).contains(&x))
                        || (y == 14 && (3..=12).contains(&x))
                }
                _ => unreachable!(),
            };
        }
    }
    board
}

fn exchange(board: &Board, selected: &[usize]) -> Result<Board> {
    let mut after = board.clone();
    for &y in selected {
        let d = y * board.n + board.n - 1;
        let p = y * board.n + board.n - 3;
        ensure!(
            board.preserved[d] && !board.preserved[p],
            "exchange endpoints at row {y}"
        );
        after.preserved[d] = false;
        after.preserved[p] = true;
    }
    // No intermediate feasibility requirement: this is one simultaneous change.
    Ok(after)
}

fn guards(board: &Board, fixture: &Fixture) -> Result<()> {
    let n = board.n;
    for &u in &fixture.protected_u {
        ensure!(!board.preserved[u], "protected U {u} changed");
    }
    for &y in &fixture.selected {
        ensure!(y >= 3 && y + 3 < n, "selected level lacks interior guards");
        ensure!(
            fixture.levels.contains(&(y - 3)) && fixture.levels.contains(&(y + 3)),
            "missing flanking levels"
        );
        for yy in y - 3..=y + 3 {
            ensure!(
                board.preserved[yy * n + n - 1],
                "broken boundary rail at {yy}"
            );
        }
        for yy in [y - 3, y, y + 3] {
            ensure!(
                board.preserved[yy * n + n - 4],
                "missing depth-three tooth at {yy}"
            );
            ensure!(
                !board.preserved[yy * n + n - 3],
                "guard hole filled at {yy}"
            );
        }
        ensure!(
            !board.preserved[y * n + n - 2],
            "rail-side neighbour is not U"
        );
    }
    for &u in &fixture.isolate_witnesses {
        ensure!(!board.preserved[u], "isolate witness {u} is F");
        ensure!(
            neighbors(n, u).all(|v| !board.preserved[v]),
            "witness {u} has a forced incident edge"
        );
    }
    Ok(())
}

fn audit_fixture(f: &Fixture) -> Result<FixtureSummary> {
    let (kind, expected_patch, expected_selected) = match f.name.as_str() {
        "rooted14_middle" => ("rooted14", rectangle(14, 9, 5, 5, 5), vec![7]),
        "rooted14_cap" => ("rooted14", rectangle(14, 8, 10, 5, 4), vec![7]),
        "rootless14_cap" => ("rootless14", rectangle(14, 8, 10, 5, 4), vec![7]),
        "rooted15_cap" => ("rooted15", rectangle(15, 9, 10, 5, 5), vec![4, 7]),
        _ => bail!("unknown batch001 fixture"),
    };
    let base = parse_rows(&f.base_rows, f.n)?;
    ensure!(base == skeleton(kind), "wrong physical skeleton");
    let expected_levels = if f.n == 15 {
        vec![1, 4, 7, 10]
    } else {
        vec![4, 7, 10]
    };
    ensure!(
        f.levels == expected_levels && f.selected == expected_selected,
        "wrong levels/selection"
    );
    ensure!(f.patch == expected_patch, "wrong patch");
    unique_indices(&f.patch, f.n * f.n, "patch")?;
    unique_indices(&f.levels, f.n, "levels")?;
    unique_indices(&f.selected, f.n, "selected")?;
    unique_indices(&f.protected_u, f.n * f.n, "protected U")?;
    unique_indices(&f.optional, f.n * f.n, "optional")?;
    let protected: Vec<_> = f.levels.iter().map(|&y| y * f.n + f.n - 3).collect();
    ensure!(f.protected_u == protected, "wrong protected U list");
    let optional: Vec<_> = f
        .patch
        .iter()
        .copied()
        .filter(|&v| !base.preserved[v] && !protected.contains(&v))
        .collect();
    ensure!(
        f.optional == optional && optional.len() <= 20,
        "wrong optional list or too many variables"
    );
    let isolates: Vec<_> = f
        .selected
        .iter()
        .flat_map(|&y| [(y - 1) * f.n + f.n - 3, (y + 1) * f.n + f.n - 3])
        .collect();
    ensure!(f.isolate_witnesses == isolates, "wrong isolate witnesses");
    unique_indices(&isolates, f.n * f.n, "isolate witnesses")?;
    guards(&base, f)?;
    let base_ledger = checked_ledger(&base)?;
    ensure!(base_ledger == f.base_ledger, "base ledger mismatch");
    let t = f.selected.len() as i64;
    // Each interior rail deletion splits one carrier, adds one boundary-hole
    // unit, and removes its horizontal FU edge (vertical edges stay forced).
    // Promotion attaches to its existing tooth carrier and adds three edges:
    // one toward the rail and two to guarded isolates. Net forced edges: +2.
    let delta = Ledger {
        f: 0,
        r: t,
        b: t,
        c: -2 * t,
        z: -2 * t,
    };
    ensure!(
        f.deltas == delta,
        "archived delta disagrees with physical formula"
    );
    let subsets = 1u64 << optional.len();
    ensure!(f.subsets == subsets, "subset count mismatch");
    ensure!(
        f.feasible_masks.iter().all(|&m| m < subsets)
            && f.feasible_masks.windows(2).all(|w| w[0] < w[1]),
        "invalid feasible mask list"
    );
    let mut feasible = 0usize;
    let mut cyclic = 0u64;
    for mask in 0..subsets {
        let mut board = base.clone();
        for (i, &v) in optional.iter().enumerate() {
            board.preserved[v] = mask & (1u64 << i) != 0;
        }
        let observation = match observe(&board) {
            Ok(o) => o,
            Err(e) => {
                ensure!(
                    e == "primal forced graph contains a cycle",
                    "mask {mask}: unexpected oracle error: {e}"
                );
                cyclic += 1;
                continue;
            }
        };
        ensure!(
            f.feasible_masks.get(feasible) == Some(&mask),
            "feasible mask list mismatch at mask {mask}"
        );
        feasible += 1;
        guards(&board, f).with_context(|| format!("mask {mask}"))?;
        let before = Ledger::from_observation(&observation);
        let after = checked_ledger(&exchange(&board, &f.selected)?)
            .with_context(|| format!("promoted mask {mask}"))?;
        ensure!(
            after.difference(&before) == delta,
            "mask {mask}: physical delta mismatch"
        );
    }
    ensure!(
        feasible == f.feasible_masks.len(),
        "archive has unmatched feasible masks"
    );
    Ok(FixtureSummary {
        name: f.name.clone(),
        n: f.n,
        optional_variables: optional.len(),
        masks_checked: subsets,
        cyclic_masks: cyclic,
        feasible_masks: feasible as u64,
        exchanges_checked: feasible as u64,
        isolate_witness_checks: feasible as u64 * isolates.len() as u64,
        base_ledger,
        verified_delta: delta,
    })
}

fn main() -> Result<()> {
    let args: Vec<_> = std::env::args_os().collect();
    ensure!(
        args.len() == 3,
        "usage: audit_guarded_fronts INPUT.json OUTPUT.json"
    );
    let batch: Batch = serde_json::from_reader(BufReader::new(File::open(&args[1])?))?;
    ensure!(
        batch.schema == 1 && batch.fixtures.len() == 4,
        "expected batch001 schema 1 with four fixtures"
    );
    let names: BTreeSet<_> = batch.fixtures.iter().map(|f| f.name.as_str()).collect();
    ensure!(
        names
            == BTreeSet::from([
                "rooted14_middle",
                "rooted14_cap",
                "rootless14_cap",
                "rooted15_cap"
            ]),
        "wrong fixture inventory"
    );
    let control = &batch.all_rows_control;
    let before_board = parse_rows(&control.before_rows, 14)?;
    let after_board = parse_rows(&control.after_rows, 14)?;
    ensure!(
        before_board == skeleton("rooted14"),
        "wrong control skeleton"
    );
    ensure!(control.selected == [4, 7, 10], "wrong control selection");
    ensure!(
        exchange(&before_board, &control.selected)? == after_board,
        "control rows do not match simultaneous exchange"
    );
    let before = checked_ledger(&before_board)?;
    let after = checked_ledger(&after_board)?;
    ensure!(
        before == control.before && after == control.after,
        "control ledger mismatch"
    );
    ensure!(
        (before.f, before.r, before.b, before.c) == (46, 7, 36, 71),
        "wrong control starting ledger"
    );
    let control_delta = after.difference(&before);
    ensure!(
        (
            control_delta.f,
            control_delta.r,
            control_delta.b,
            control_delta.c
        ) == (0, 2, 3, -5),
        "wrong all-rows control delta"
    );
    // Six promotion-adjacent isolates disappear; clearing the rail endpoint
    // at row 10 creates one new isolate immediately below it, at (13, 11).
    ensure!(
        control_delta.z == -5,
        "wrong all-rows control isolate delta"
    );
    // Fail early on an existing output; a failed audit never writes a success summary.
    let output = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&args[2])?;
    let mut summaries = Vec::new();
    for fixture in &batch.fixtures {
        summaries.push(audit_fixture(fixture).with_context(|| fixture.name.clone())?);
    }
    let masks: u64 = summaries.iter().map(|s| s.masks_checked).sum();
    let feasible: u64 = summaries.iter().map(|s| s.feasible_masks).sum();
    ensure!(masks == 393_216, "incomplete batch001 enumeration: {masks}");
    let summary = serde_json::json!({
        "schema": 1,
        "validated": true,
        "input": args[1].to_string_lossy(),
        "oracle": "grid_graphs::certificate_corpus::observe; literal Rust primal traversal",
        "scope": "complete four batch001 optional-extension families; finite audit, not a uniform theorem or global optimization",
        "checks": ["exact skeletons, patches, levels and frozen labels", "optional list completeness and exact feasible mask lists", "literal rail/guard and isolated-hole witnesses", "simultaneous exchanges and all five physical ledger deltas", "all-rows endpoint control"],
        "masks_checked": masks,
        "feasible_masks": feasible,
        "cyclic_masks": masks - feasible,
        "exchanges_checked": feasible,
        "all_rows_control": {"before": before, "after": after, "delta": control_delta},
        "fixtures": summaries,
    });
    let mut writer = BufWriter::new(output);
    serde_json::to_writer_pretty(&mut writer, &summary)?;
    writeln!(writer)?;
    writer.flush()?;
    Ok(())
}
