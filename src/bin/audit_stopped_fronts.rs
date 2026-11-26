//! Literal Rust audit of the two finite stopped-front batch001 families.
use anyhow::{anyhow, ensure, Context, Result};
use grid_graphs::certificate_corpus::{observe, Board};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};
use std::fs::{File, OpenOptions};
use std::io::{BufReader, BufWriter, Write};

#[derive(Debug, Deserialize, Serialize, PartialEq, Eq)]
struct Example {
    mask: u64,
    isolates: Vec<usize>,
    right_side_hole_units: Vec<usize>,
    rail_root_count: usize,
}

#[derive(Deserialize)]
struct Fixture {
    n: usize,
    levels: Vec<usize>,
    base_rows: Vec<String>,
    optional: Vec<usize>,
    first_free: usize,
    last_free: usize,
    subsets: u64,
    feasible_masks: Vec<u64>,
    demand_numerator: i64,
    demand_denominator: i64,
    invoice_histogram: BTreeMap<String, u64>,
    examples: BTreeMap<String, Example>,
    corner_hole_cases: u64,
}

#[derive(Deserialize)]
struct Batch {
    schema: u32,
    fixtures: Vec<Fixture>,
}

#[derive(Serialize)]
struct Summary {
    n: usize,
    optional_variables: usize,
    masks_checked: u64,
    feasible_masks: u64,
    cyclic_masks: u64,
    invoices_checked: u64,
    invoice_units_checked: u64,
    units_per_invoice: usize,
    demand_numerator: i64,
    demand_denominator: i64,
    invoice_histogram: BTreeMap<String, u64>,
    corner_hole_cases: u64,
    examples_checked: usize,
}

// Board::neighbors is crate-private. These are physical grid neighbours,
// not bank-incidence or virtual exterior connections.
fn neighbors(n: usize, v: usize) -> impl Iterator<Item = usize> {
    [
        (v % n > 0).then(|| v - 1),
        (v % n + 1 < n).then(|| v + 1),
        (v / n > 0).then(|| v - n),
        (v / n + 1 < n).then(|| v + n),
    ]
    .into_iter()
    .flatten()
}

// Ancillary example check only. Feasibility for EVERY mask is decided by
// certificate_corpus::observe, independently of Python's component routine.
fn rail_root_count(board: &Board, levels: &[usize]) -> usize {
    let mut roots = vec![usize::MAX; board.n * board.n];
    for start in 0..roots.len() {
        if roots[start] != usize::MAX {
            continue;
        }
        roots[start] = start;
        let mut stack = vec![start];
        while let Some(v) = stack.pop() {
            for w in neighbors(board.n, v) {
                if (board.preserved[v] || board.preserved[w]) && roots[w] == usize::MAX {
                    roots[w] = start;
                    stack.push(w);
                }
            }
        }
    }
    levels
        .iter()
        .map(|&y| roots[y * board.n + board.n - 4])
        .collect::<BTreeSet<_>>()
        .len()
}

fn audit(f: &Fixture) -> Result<Summary> {
    ensure!((1..=15).contains(&f.n), "side exceeds audit limit");
    let (levels, first_free, last_free) = match f.n {
        11 => (vec![2, 5, 8], 1, 9),
        14 => (vec![4, 7, 10, 13], 4, 13),
        _ => return Err(anyhow!("unexpected batch001 side {}", f.n)),
    };
    ensure!(f.levels == levels, "wrong rail levels");
    ensure!(
        f.first_free == first_free && f.last_free == last_free,
        "wrong free-row interval"
    );
    let n = f.n;
    let width = n - 1; // A in the declared demand formula.
    let gaps = levels.len() - 1; // a, distinct from A.
    let mut base = Board {
        n,
        preserved: vec![false; n * n],
    };
    for &y in &levels {
        for x in 0..=width - 3 {
            base.preserved[y * n + x] = true;
        }
    }
    // Exact canonical rows also exclude hidden fixed F labels or a spine.
    ensure!(
        f.base_rows == base.rows(),
        "base differs from stopped-rail skeleton"
    );
    let optional: Vec<_> = (first_free..=last_free)
        .flat_map(|y| [y * n + width - 1, y * n + width])
        .collect();
    ensure!(
        f.optional == optional && optional.len() <= 20,
        "optional list mismatch or limit exceeded"
    );
    let subsets = 1u64 << optional.len();
    ensure!(f.subsets == subsets, "wrong declared subset count");
    ensure!(
        f.feasible_masks.iter().all(|&m| m < subsets)
            && f.feasible_masks.windows(2).all(|w| w[0] < w[1]),
        "invalid feasible-mask list"
    );
    let offlevels: Vec<_> = (levels[0] + 1..*levels.last().unwrap())
        .filter(|y| !levels.contains(y))
        .collect();
    ensure!(offlevels.len() == 2 * gaps, "wrong off-level count");
    let demand_numerator = gaps as i64 * (2 * width as i64 - 9);
    let demand_denominator = width as i64;
    ensure!(
        f.demand_numerator == demand_numerator && f.demand_denominator == demand_denominator,
        "declared demand differs from a*(2A-9)/A"
    );
    // Verify the only POSSIBLE F neighbour condition against the entire family,
    // rather than inferring it from individual feasible samples.
    for &y in &offlevels {
        let u = y * n + width - 2;
        let s = y * n + width - 1;
        ensure!(
            !base.preserved[u] && !optional.contains(&u),
            "invoice u is not frozen U"
        );
        for v in neighbors(n, u).filter(|&v| v != s) {
            ensure!(
                !base.preserved[v] && !optional.contains(&v),
                "u has another possible F neighbour"
            );
        }
    }
    let mut feasible = 0usize;
    let mut cyclic = 0u64;
    let mut histogram = BTreeMap::<String, u64>::new();
    let mut examples = BTreeMap::<String, Example>::new();
    let mut corner_hole_cases = 0u64;
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
            "feasible-mask mismatch at mask {mask}"
        );
        feasible += 1;
        let mut isolates = Vec::new();
        let mut holes = Vec::new();
        // Resource identity includes its kind and boundary side. A corner's
        // right unit is ONE b unit, not both its right and bottom units.
        let mut units = BTreeSet::new();
        for &y in &offlevels {
            let u = y * n + width - 2;
            let s = y * n + width - 1;
            let h = (y + 1) * n + width;
            ensure!(!board.preserved[u], "mask {mask}: u={u} is not U");
            if board.preserved[s] {
                ensure!(
                    h < n * n && h % n == width && !board.preserved[h],
                    "mask {mask}: invalid right-side hole at {h}"
                );
                ensure!(
                    4 - neighbors(n, h).count() >= 1,
                    "missing physical deficiency unit"
                );
                ensure!(
                    units.insert(("b:right", h)),
                    "reused right-side deficiency unit"
                );
                holes.push(h);
            } else {
                ensure!(
                    neighbors(n, u).all(|v| !board.preserved[v]),
                    "mask {mask}: u={u} is not an actual isolate"
                );
                ensure!(units.insert(("z", u)), "reused isolate unit");
                isolates.push(u);
            }
        }
        ensure!(
            units.len() == 2 * gaps && isolates.len() + holes.len() == 2 * gaps,
            "wrong invoice size"
        );
        ensure!(
            isolates.len() as i64 <= observation.features["z"]
                && holes.len() as i64 <= observation.features["b"],
            "invoice exceeds actual resource counts"
        );
        ensure!(
            demand_numerator <= demand_denominator * units.len() as i64,
            "invoice fails integer demand"
        );
        if holes.contains(&(n * n - 1)) {
            ensure!(
                neighbors(n, n * n - 1).count() == 2,
                "corner deficiency is not two"
            );
            corner_hole_cases += 1;
        }
        let key = format!("z{}_h{}", isolates.len(), holes.len());
        *histogram.entry(key.clone()).or_default() += 1;
        // Python archives the FIRST feasible mask of each invoice type.
        examples.entry(key).or_insert_with(|| Example {
            mask,
            isolates,
            right_side_hole_units: holes,
            rail_root_count: rail_root_count(&board, &levels),
        });
    }
    ensure!(
        feasible == f.feasible_masks.len(),
        "unmatched archived feasible masks"
    );
    ensure!(
        histogram == f.invoice_histogram,
        "invoice histogram mismatch"
    );
    ensure!(
        corner_hole_cases == f.corner_hole_cases,
        "corner-hole count mismatch"
    );
    ensure!(
        examples == f.examples,
        "example masks, witnesses, or actual rail root counts mismatch"
    );
    Ok(Summary {
        n,
        optional_variables: optional.len(),
        masks_checked: subsets,
        feasible_masks: feasible as u64,
        cyclic_masks: cyclic,
        invoices_checked: feasible as u64,
        invoice_units_checked: feasible as u64 * (2 * gaps) as u64,
        units_per_invoice: 2 * gaps,
        demand_numerator,
        demand_denominator,
        invoice_histogram: histogram,
        corner_hole_cases,
        examples_checked: examples.len(),
    })
}

fn main() -> Result<()> {
    let args: Vec<_> = std::env::args_os().collect();
    ensure!(
        args.len() == 3,
        "usage: audit_stopped_fronts INPUT.json OUTPUT.json"
    );
    let batch: Batch = serde_json::from_reader(BufReader::new(File::open(&args[1])?))?;
    ensure!(
        batch.schema == 1 && batch.fixtures.len() == 2,
        "expected schema 1 and two fixtures"
    );
    ensure!(
        batch.fixtures.iter().map(|f| f.n).collect::<BTreeSet<_>>() == BTreeSet::from([11, 14]),
        "wrong batch001 fixture inventory"
    );
    // Exclusive creation before expensive enumeration. Failure may leave an
    // empty file, but never a success summary; reruns require a fresh path.
    let output = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&args[2])?;
    let mut summaries = Vec::new();
    for fixture in &batch.fixtures {
        summaries.push(audit(fixture).with_context(|| format!("stopped{}", fixture.n))?);
    }
    let masks: u64 = summaries.iter().map(|s| s.masks_checked).sum();
    let feasible: u64 = summaries.iter().map(|s| s.feasible_masks).sum();
    let units: u64 = summaries.iter().map(|s| s.invoice_units_checked).sum();
    ensure!(masks == 1_310_720, "incomplete batch001 enumeration");
    let summary = serde_json::json!({
        "schema": 1,
        "validated": true,
        "input": args[1].to_string_lossy(),
        "oracle": "grid_graphs::certificate_corpus::observe",
        "scope": "complete specified stopped-front two-column exterior families; finite computational audit, not a uniform theorem",
        "checks": ["exact stopped-rail skeletons and optional variables", "every mask: literal primal feasibility and exact archived feasible list", "every feasible mask: actual isolate or distinct right-side deficiency witnesses", "exact integer demand and 2a invoice units", "invoice histograms and corner-hole cases", "first example masks, witness lists and actual rail component counts"],
        "masks_checked": masks,
        "feasible_masks": feasible,
        "cyclic_masks": masks - feasible,
        "invoices_checked": feasible,
        "invoice_units_checked": units,
        "fixtures": summaries,
    });
    let mut writer = BufWriter::new(output);
    serde_json::to_writer_pretty(&mut writer, &summary)?;
    writeln!(writer)?;
    writer.flush()?;
    Ok(())
}
