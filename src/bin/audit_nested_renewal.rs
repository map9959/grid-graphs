//! Scheduled finite batch003 audit; fixed repository inputs, only n=8,14.
//! Run from the repository: audit_nested_renewal --output data/NEW.json
//! Output is compact JSON, reserved with create_new; no solver or Python runs.
use anyhow::{anyhow, ensure, Context, Result};
use grid_graphs::certificate_corpus::{observe, Board};
use serde_json::{json, Value};
use std::collections::BTreeSet;
use std::fs::{self, OpenOptions};
use std::io::Write;
use std::path::Path;

const INPUT: &str = "data/nested_renewal_batch003_cycle3.json";
const RECORDS: [&str; 2] = [
    "data/renewal_annulus_n8_batch002.json",
    "data/renewal_annulus_n14_gap1_batch002.json",
];
type Set = BTreeSet<usize>;

fn array(v: &Value) -> Result<&Vec<Value>> {
    v.as_array().context("expected array")
}
fn number(v: &Value) -> Result<usize> {
    usize::try_from(v.as_u64().context("expected nonnegative integer")?).context("integer overflow")
}
fn ids(v: &Value) -> Result<Vec<usize>> {
    array(v)?.iter().map(number).collect()
}
fn equal(actual: Value, expected: &Value, label: &str) -> Result<()> {
    ensure!(
        &actual == expected,
        "{label}: actual {actual}, expected {expected}"
    );
    Ok(())
}
fn depth(n: usize, v: usize) -> usize {
    (v / n).min(v % n).min(n - 1 - v / n).min(n - 1 - v % n)
}
fn neighbors(n: usize, v: usize) -> impl Iterator<Item = usize> {
    [
        (v / n > 0).then(|| v - n),
        (v % n > 0).then(|| v - 1),
        (v % n + 1 < n).then(|| v + 1),
        (v / n + 1 < n).then(|| v + n),
    ]
    .into_iter()
    .flatten()
}
fn board(n: usize, f: &Set) -> Board {
    assert!(matches!(n, 8 | 14));
    assert!(f.iter().all(|&v| v < n * n));
    Board {
        n,
        preserved: (0..n * n).map(|v| f.contains(&v)).collect(),
    }
}
fn coords(n: usize, f: &[usize]) -> Value {
    json!(f.iter().map(|&v| [v / n, v % n]).collect::<Vec<_>>())
}
fn components(adj: &[Vec<usize>], active: &[bool]) -> (usize, usize) {
    let mut seen = vec![false; adj.len()];
    let (mut count, mut isolates) = (0, 0);
    for start in 0..adj.len() {
        if !active[start] || seen[start] {
            continue;
        }
        count += 1;
        isolates += usize::from(adj[start].is_empty());
        seen[start] = true;
        let mut stack = vec![start];
        while let Some(v) = stack.pop() {
            for &w in &adj[v] {
                if !seen[w] {
                    seen[w] = true;
                    stack.push(w);
                }
            }
        }
    }
    (count, isolates)
}

// Incremental accepted-forest path, independent of observe and Python traversal.
// If endpoints are already connected, the path plus the new edge is a cycle.
fn cycle(n: usize, f: &Set) -> Result<Option<Vec<usize>>> {
    let mut accepted = vec![Vec::new(); n * n];
    for u in 0..n * n {
        for v in neighbors(n, u).filter(|&v| v > u) {
            if !(f.contains(&u) || f.contains(&v)) {
                continue;
            }
            let mut parent = vec![usize::MAX; n * n];
            parent[u] = u;
            let mut stack = vec![u];
            while let Some(x) = stack.pop() {
                if x == v {
                    break;
                }
                for &y in &accepted[x] {
                    if parent[y] == usize::MAX {
                        parent[y] = x;
                        stack.push(y);
                    }
                }
            }
            if parent[v] != usize::MAX {
                let mut path = vec![v];
                let mut x = v;
                while x != u {
                    x = parent[x];
                    path.push(x);
                }
                path.reverse();
                path.push(u);
                ensure!(
                    path.len() >= 5 && path.first() == path.last(),
                    "invalid cycle closure"
                );
                ensure!(
                    path[..path.len() - 1]
                        .iter()
                        .copied()
                        .collect::<Set>()
                        .len()
                        == path.len() - 1,
                    "cycle is not simple"
                );
                for e in path.windows(2) {
                    ensure!(
                        neighbors(n, e[0]).any(|w| w == e[1])
                            && (f.contains(&e[0]) || f.contains(&e[1])),
                        "invalid forced cycle edge"
                    );
                }
                return Ok(Some(path));
            }
            accepted[u].push(v);
            accepted[v].push(u);
        }
    }
    Ok(None)
}

// Recompute the complete source ledger even for rejected boards. Native observe
// remains the feasibility oracle; unexpected oracle errors are never rejections.
fn ledger(n: usize, f: &Set) -> Result<Value> {
    let bboard = board(n, f);
    let native = match observe(&bboard) {
        Ok(o) => Some(o),
        Err(e) => {
            ensure!(e == "primal forced graph contains a cycle", "observe: {e}");
            None
        }
    };
    let mut adj = vec![Vec::new(); n * n];
    let mut ff = adj.clone();
    let (mut edges, mut ff_edges, mut b) = (0usize, 0usize, 0usize);
    for u in 0..n * n {
        if !f.contains(&u) {
            b += 4 - neighbors(n, u).count();
        }
        for v in neighbors(n, u).filter(|&v| v > u) {
            if f.contains(&u) || f.contains(&v) {
                edges += 1;
                adj[u].push(v);
                adj[v].push(u);
            }
            if f.contains(&u) && f.contains(&v) {
                ff_edges += 1;
                ff[u].push(v);
                ff[v].push(u);
            }
        }
    }
    let (c, z) = components(&adj, &vec![true; n * n]);
    let (r, _) = components(&ff, &bboard.preserved);
    let beta = edges as i64 - (n * n) as i64 + c as i64;
    let ff_beta = ff_edges as i64 - f.len() as i64 + r as i64;
    let residual = (3 * f.len() + r + b + c) as i64 - (n * n + 4 * n) as i64;
    ensure!(
        native.is_some() == (beta == 0),
        "native/independent rank disagreement"
    );
    if let Some(o) = native {
        for (key, val) in [
            ("f", f.len()),
            ("r", r),
            ("b", b),
            ("c", c),
            ("z", z),
            ("forced_edges", edges),
        ] {
            ensure!(
                o.features.get(key) == Some(&(val as i64)),
                "native {key} mismatch"
            );
        }
        ensure!(residual == 0 && ff_beta == 0, "forest ledger mismatch");
    }
    Ok(json!({"f":f.len(),"r":r,"b":b,"c":c,"z":z,"edges":edges,
        "ff_edges":ff_edges,"cycle_rank":beta,"ff_cycle_rank":ff_beta,
        "forest":beta==0,"forest_ledger_residual":residual}))
}
fn check_board(n: usize, f: &Set, v: &Value, historical: bool) -> Result<Value> {
    let listed = ids(&v["center_ids"])?;
    equal(json!(f), &v["center_ids"], "center_ids")?;
    ensure!(listed.iter().all(|&x| x < n * n), "out of range center");
    equal(coords(n, &listed), &v["centers"], "coordinates")?;
    let rows: Vec<String> = (0..n)
        .map(|r| {
            (0..n)
                .map(|c| {
                    if f.contains(&(r * n + c)) {
                        if historical {
                            '.'
                        } else {
                            'F'
                        }
                    } else {
                        'U'
                    }
                })
                .collect()
        })
        .collect();
    equal(json!(rows), &v["rows"], "authoritative rows")?;
    if !historical {
        equal(json!(n), &v["n"], "board size")?;
    }
    let stats = ledger(n, f)?;
    equal(stats.clone(), &v["ledger"], "board ledger")?;
    Ok(stats)
}

fn reconstruct(n: usize) -> Result<(Set, Set, Value)> {
    ensure!(matches!(n, 8 | 14), "unauthorized size");
    let k = (n - 2) / 3;
    let mut source = Set::new();
    // source_i: A_i, B_i, diagonal singletons, inclusive source intervals.
    for i in 1..k {
        for r in 2..=3 * i {
            source.insert(r * n + 3 * i + 1);
        }
    }
    for i in 0..k - 1 {
        for r in 3 * i + 5..3 * k {
            source.insert(r * n + 3 * i + 3);
        }
    }
    for a in 0..k {
        source.insert((3 * a + 2) * n + 3 * a + 2);
    }
    let mut top = Set::new();
    let mut bottom = Set::new();
    for i in 1..k {
        for r in 0..2 {
            top.insert(r * n + 3 * i + 1);
        }
    }
    for i in 0..k - 1 {
        for r in 3 * k..n {
            bottom.insert(r * n + 3 * i + 3);
        }
    }
    let left: Set = (2..n).map(|r| r * n).collect();
    let right: Set = (0..n - 1).map(|r| r * n + n - 1).collect();
    let singleton = Set::from([1]); // coordinate (0,1), not two singleton IDs.
    let parts = [source.clone(), top, bottom, left, right, singleton];
    let mut q = Set::new();
    for part in &parts {
        ensure!(q.is_disjoint(part), "Q reconstruction pieces overlap");
        q.extend(part);
    }
    let names = [
        "source_i",
        "top_extensions",
        "bottom_extensions",
        "left_rod",
        "right_rod",
        "singleton_0_1",
    ];
    let pieces: Vec<_> = names
        .iter()
        .zip(&parts)
        .map(|(name, p)| json!({"piece":name,"count":p.len(),"ids":p}))
        .collect();
    Ok((q, source, json!(pieces)))
}
fn promoted(q: &Set, extras: &[usize]) -> Set {
    q.iter().copied().chain(extras.iter().copied()).collect()
}
fn trial(n: usize, q: &Set, extras: &[usize]) -> Result<Value> {
    Ok(
        json!({"extra_ids":extras,"extras":coords(n, extras),"ledger":ledger(n,&promoted(q,extras))?}),
    )
}

fn audit(root: &Path) -> Result<Value> {
    let raw: Value = serde_json::from_slice(&fs::read(root.join(INPUT))?)?;
    equal(json!("nested_renewal_cycle3_v1"), &raw["schema"], "schema")?;
    equal(json!("completed"), &raw["status"], "status")?;
    equal(
        json!([8, 14]),
        &raw["source_coordinate_scope"]["materialized_sizes"],
        "sizes",
    )?;
    equal(
        json!(false),
        &raw["source_coordinate_scope"]["larger_board_materialized"],
        "size cap",
    )?;
    let cases = array(&raw["cases"])?;
    ensure!(cases.len() == 2, "expected two cases");
    let mut reports = Vec::new();
    let mut qs = Vec::new();
    let mut records = Vec::new();
    let mut feasible_pairs = Vec::new();
    for (index, n) in [8usize, 14].into_iter().enumerate() {
        let case = &cases[index];
        let k = (n - 2) / 3;
        equal(json!(n), &case["n"], "case n")?;
        equal(json!(k), &case["k"], "case k")?;
        let (q, source, pieces) = reconstruct(n)?;
        let deep: Set = (0..n * n).filter(|&v| depth(n, v) >= 3).collect();
        let core: Set = q.intersection(&deep).copied().collect();
        ensure!(
            core == source.intersection(&deep).copied().collect(),
            "deep F mismatch"
        );
        let deep_u: Set = deep.difference(&q).copied().collect();
        ensure!(
            deep_u == deep.difference(&source).copied().collect(),
            "deep U mismatch"
        );
        let counts = json!({"q_f":q.len(),"deep_f":core.len(),"old_band_f":q.len()-core.len()});
        ensure!(
            q.len() == 3 * k * k + 5 * k + 1
                && core.len() == 3 * k * k + 3 - 7 * k
                && q.len() - core.len() == 12 * k - 2,
            "finite polynomial counts"
        );
        equal(counts.clone(), &case["expected_counts"], "expected counts")?;
        equal(counts.clone(), &case["observed_counts"], "observed counts")?;
        equal(json!(core), &case["immutable_deep_f_ids"], "deep F")?;
        equal(json!(deep_u), &case["immutable_deep_u_ids"], "deep U")?;
        equal(
            json!(true),
            &case["source_deep_labels_agree"],
            "deep agreement flag",
        )?;
        equal(json!(3 * k * k + 7 * k), &case["target"], "target")?;
        equal(json!(2 * k - 1), &case["crop_deficit"], "deficit")?;
        ensure!(
            check_board(n, &q, &case["q"], false)?["forest"] == true,
            "Q cyclic"
        );
        let holes: Vec<_> = (0..n * n)
            .filter(|v| depth(n, *v) < 3 && !q.contains(v))
            .collect();
        equal(json!(holes), &case["allowed_hole_ids"], "hole IDs")?;
        equal(
            coords(n, &holes),
            &case["allowed_holes"],
            "hole coordinates",
        )?;
        let singles = &case["single_promotions"];
        let trials = array(&singles["trials"])?;
        ensure!(trials.len() == holes.len(), "singleton list length");
        let mut eligible = Vec::new();
        let mut rejected = Vec::new();
        let mut cycles = Vec::new();
        for (&v, recorded) in holes.iter().zip(trials) {
            let f = promoted(&q, &[v]);
            let stats = ledger(n, &f)?;
            equal(
                json!({"id":v,"coordinate":[v/n,v%n],"ledger":stats}),
                recorded,
                "singleton trial",
            )?;
            let witness = cycle(n, &f)?;
            ensure!(
                witness.is_none() == (stats["forest"] == true),
                "cycle/oracle disagreement"
            );
            if let Some(path) = witness {
                ensure!(
                    path.contains(&v),
                    "rejection cycle does not use promoted vertex"
                );
                rejected.push(v);
                cycles.push(json!({"promotion_id":v,"cycle_vertices":path}));
            } else {
                eligible.push(v);
            }
        }
        ensure!(
            eligible == vec![0, n * n - 1],
            "eligible pool is not exactly opposite corners"
        );
        equal(json!(holes.len()), &singles["tested"], "single count")?;
        equal(json!(eligible), &singles["eligible_ids"], "eligible IDs")?;
        equal(
            coords(n, &eligible),
            &singles["eligible"],
            "eligible coordinates",
        )?;
        equal(
            json!(rejected),
            &singles["ineligible_ids"],
            "ineligible IDs",
        )?;
        let mut pair_summary = Value::Null;
        if n == 8 {
            ensure!(holes.len() == 38 && deep_u.len() == 3, "n8 hole partition");
            let mut accepted = Vec::new();
            let mut denied = Vec::new();
            for i in 0..holes.len() {
                for j in i + 1..holes.len() {
                    let t = trial(n, &q, &[holes[i], holes[j]])?;
                    if t["ledger"]["forest"] == true {
                        accepted.push(t);
                    } else {
                        denied.push(t);
                    }
                }
            }
            ensure!(accepted.len() + denied.len() == 703, "pair coverage");
            equal(
                json!({"status":"exhaustive","tested":703,"feasible_count":accepted.len(),
                "feasible_25_pairs":accepted,"rejected_pairs":denied,"decision":"sat"}),
                &case["pairs"],
                "complete pair partition and ledgers",
            )?;
            feasible_pairs = accepted
                .iter()
                .map(|t| ids(&t["extra_ids"]))
                .collect::<Result<_>>()?;
            ensure!(
                feasible_pairs == vec![vec![0, 63]],
                "unexpected feasible pair list"
            );
            pair_summary = json!({"tested":703,"rejected":denied.len(),"feasible_pairs":feasible_pairs,
                "exact_artifact_lists_and_ledgers":true});
        }
        let sup = &case["supersets"];
        let (mut masks, mut best_masks, mut best) = (Vec::new(), Vec::new(), 0usize);
        let mut subset_trials = Vec::new();
        for mask in 0usize..4 {
            let extra: Vec<_> = eligible
                .iter()
                .enumerate()
                .filter_map(|(i, &v)| (mask & (1 << i) != 0).then_some(v))
                .collect();
            let f = promoted(&q, &extra);
            let stats = ledger(n, &f)?;
            if stats["forest"] == true {
                masks.push(mask);
                if f.len() > best {
                    best = f.len();
                    best_masks.clear();
                }
                if f.len() == best {
                    best_masks.push(mask);
                }
            }
            subset_trials.push(json!({"mask":mask,"extra_ids":extra,"ledger":stats}));
        }
        ensure!(best == if n == 8 { 25 } else { 71 }, "superset maximum");
        for (key, val) in [
            ("eligible_ids", json!(eligible)),
            ("total_supermasks", json!(4)),
            ("tested_supermasks", json!(4)),
            ("feasible_supermask_count", json!(masks.len())),
            ("feasible_masks", json!(masks)),
            ("maximum_f", json!(best)),
            ("best_masks", json!(best_masks)),
            ("exhaustive", json!(true)),
            ("pool_limit", json!(20)),
            ("mask_encoding", json!("bit i selects eligible_ids[i]")),
            ("status", json!("exact_core_compatible_superset_optimum")),
        ] {
            equal(val, &sup[key], key)?;
        }
        let best_boards = array(&sup["best_boards"])?;
        ensure!(best_boards.len() == best_masks.len(), "best boards length");
        for (&mask, recorded) in best_masks.iter().zip(best_boards) {
            let extra: Vec<_> = eligible
                .iter()
                .enumerate()
                .filter_map(|(i, &v)| (mask & (1 << i) != 0).then_some(v))
                .collect();
            check_board(n, &promoted(&q, &extra), recorded, false)?;
        }
        let original: Value = serde_json::from_slice(&fs::read(root.join(RECORDS[index]))?)?;
        equal(json!(n), &original["n"], "original size")?;
        equal(
            json!("sat_verified"),
            &original["status"],
            "original status",
        )?;
        let old: Set = ids(&original["witness"]["center_ids"])?
            .into_iter()
            .collect();
        ensure!(
            check_board(n, &old, &original["witness"], true)?["forest"] == true,
            "original cyclic"
        );
        ensure!(old.len() == if n == 8 { 26 } else { 75 }, "original count");
        let rewrite = &case["recorded_seed_rewrite"];
        equal(json!(RECORDS[index]), &rewrite["source"], "original source")?;
        check_board(n, &old, &rewrite["board"], false)?;
        let delete: Vec<_> = old.difference(&q).copied().collect();
        let add: Vec<_> = q.difference(&old).copied().collect();
        ensure!(
            (delete.len(), add.len()) == if n == 8 { (10, 7) } else { (18, 12) },
            "mandatory rewrite counts"
        );
        ensure!(
            delete.iter().chain(&add).all(|&v| depth(n, v) < 3),
            "rewrite outside old band"
        );
        for (key, val) in [
            ("delete_ids", json!(delete)),
            ("add_ids", json!(add)),
            ("delete", coords(n, &delete)),
            ("add", coords(n, &add)),
            ("delete_count", json!(delete.len())),
            ("add_count", json!(add.len())),
            ("mandatory_flips", json!(delete.len() + add.len())),
            ("net_deleted", json!(delete.len() - add.len())),
            ("all_changes_in_old_band", json!(true)),
            ("C", json!(3 * k * k + 7 * k - old.len())),
        ] {
            equal(val, &rewrite[key], key)?;
        }
        reports.push(json!({"n":n,"k":k,"pieces":pieces,"counts":counts,
            "checks":{"disjoint_reconstruction":true,"q_rows_ids_ledger":true,
                "same_old_deep_f_and_u":true,"finite_count_formulas":true,
                "singleton_lists_and_ledgers":true,"subset_lists_maxima_boards":true,
                "original_witness_rows_ids_ledger":true,"rewrite_exact_and_in_old_band":true},
            "singleton_count":holes.len(),"eligible_ids":eligible,"rejected_count":rejected.len(),
            "rejection_cycles":cycles,"pairs":pair_summary,"subset_trials":subset_trials,
            "feasible_masks":masks,"best_masks":best_masks,"maximum_f":best,
            "rewrite":{"original_f":old.len(),"delete_ids":delete,"add_ids":add,
                "mandatory_flips":delete.len()+add.len()}}));
        qs.push(q);
        records.push(old);
    }
    let compositions = array(&raw["compositions"])?;
    ensure!(
        compositions.len() == feasible_pairs.len(),
        "composition coverage"
    );
    let final_board = &records[1];
    let embedded: Set = qs[0]
        .iter()
        .map(|&v| (v / 8 + 3) * 14 + v % 8 + 3)
        .collect();
    ensure!(
        embedded
            == final_board
                .iter()
                .copied()
                .filter(|&v| depth(14, v) >= 3)
                .collect(),
        "central crop"
    );
    let outer: Vec<_> = final_board.difference(&embedded).copied().collect();
    ensure!(
        outer.len() == 52 && outer.iter().all(|&v| depth(14, v) < 3),
        "original outer frame"
    );
    let mut composition_reports = Vec::new();
    for (extras, recorded) in feasible_pairs.iter().zip(compositions) {
        let mut current = promoted(&qs[0], extras);
        ensure!(current.len() == 25 && extras.len() == 2, "composition seed");
        let stages = array(&recorded["stages"])?;
        ensure!(stages.len() == 56, "composition stage count");
        let mut stage_reports = Vec::new();
        for (i, stage) in stages.iter().enumerate() {
            let (n, operation, id) = match i {
                0 => (8, "seed", None),
                1..=2 => {
                    let v = extras[i - 1];
                    ensure!(current.remove(&v), "delete missing extra");
                    if i == 2 {
                        ensure!(current == qs[0], "deletions not Q2");
                    }
                    (8, "delete_old_extra", Some(v))
                }
                3 => {
                    current = embedded.clone();
                    (14, "embed_plus_3_plus_3", None)
                }
                _ => {
                    let v = outer[i - 4];
                    ensure!(current.insert(v), "duplicate outer addition");
                    (14, "add_recorded_outer_F", Some(v))
                }
            };
            equal(
                json!(operation),
                &stage["operation"],
                "composition operation",
            )?;
            if let Some(v) = id {
                equal(json!(v), &stage["id"], "composition ID")?;
                equal(
                    json!([v / n, v % n]),
                    &stage["coordinate"],
                    "composition coordinate",
                )?;
            } else {
                ensure!(
                    stage.get("id").is_none() && stage.get("coordinate").is_none(),
                    "unexpected stage ID"
                );
            }
            let stats = check_board(n, &current, &stage["board"], false)?;
            ensure!(stats["forest"] == true, "cyclic stage {i}");
            stage_reports
                .push(json!({"stage":i,"n":n,"operation":operation,"id":id,"ledger":stats}));
        }
        ensure!(
            &current == final_board && current.len() == 75,
            "composition final"
        );
        for (key, val) in [
            ("extra_ids", json!(extras)),
            ("extras", coords(8, extras)),
            ("central_crop_equals_embedded_q2", json!(true)),
            ("deleted", json!(2)),
            ("added", json!(52)),
            ("net_gain", json!(50)),
            ("all_stages_forest", json!(true)),
        ] {
            equal(val, &recorded[key], key)?;
        }
        composition_reports.push(json!({"extra_ids":extras,"deleted":2,"added":52,
            "original_outer_ids":outer,"final_f":75,"net_gain":50,"stages":stage_reports}));
    }
    equal(
        json!(true),
        &raw["recorded_central_crop_equals_embedded_q2"],
        "crop flag",
    )?;
    equal(
        json!(true),
        &raw["all_superset_optima_exact"],
        "optima flag",
    )?;
    equal(
        json!("verified"),
        &raw["composition_status"],
        "composition status",
    )?;
    Ok(
        json!({"schema":"audit_nested_renewal_v1","status":"passed","input":INPUT,
        "original_inputs":RECORDS,"materialized_sizes":[8,14],"cases":reports,
        "compositions":composition_reports,"checks":{"all_requested_finite_checks":true},
        "proof_scope":{
            "kind":"finite constructive proof for these exact n8/n14 boards",
            "optimum_domain":"forest supersets of Q2/Q4 preserving all old depth>=3 F/U labels",
            "exclusion":"Every rejected singleton has a checked simple closed forced-grid cycle. Every superset containing that promotion retains every cycle edge, even if additional deep labels are promoted. With deep U fixed, all remaining candidates are the four eligible-pool subsets.",
            "cycle_encoding":"zero-based row-major vertex IDs; first vertex repeated at end",
            "symbolic_all_size_claims_proved":false,"global_optimality_claimed":false,
            "n20_materialized":false,"recorded_solver_unsat_audited":false,
            "source_sha256_recomputed":false,
            "count_formula_scope":"evaluated only at k=2,4; k=2 is the source diagnostic extension"
        }}),
    )
}

fn main() -> Result<()> {
    let args: Vec<_> = std::env::args_os().skip(1).collect();
    ensure!(
        args.len() == 2 && args[0] == "--output",
        "usage: audit_nested_renewal --output data/NEW.json"
    );
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).canonicalize()?;
    let output = Path::new(&args[1]);
    let output = if output.is_absolute() {
        output.to_path_buf()
    } else {
        root.join(output)
    };
    let parent = output.parent().context("output parent")?.canonicalize()?;
    ensure!(
        parent.starts_with(&root),
        "output must be in repository with existing parent"
    );
    let output = parent.join(output.file_name().context("output filename")?);
    // Reserve before any computation; an existing artifact is never overwritten.
    let mut handle = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&output)
        .with_context(|| format!("reserve {}", output.display()))?;
    let result = audit(&root);
    let value = match &result {
        Ok(v) => v.clone(),
        Err(e) => {
            json!({"schema":"audit_nested_renewal_v1","status":"failed","error":format!("{e:#}")})
        }
    };
    serde_json::to_writer(&mut handle, &value)?;
    handle.write_all(b"\n")?;
    handle.flush()?;
    println!("{}", json!({"output":output,"status":value["status"]}));
    result
        .map(|_| ())
        .map_err(|e| anyhow!("audit failed: {e:#}"))
}
