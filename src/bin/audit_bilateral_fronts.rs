//! Independent batch003 audit. Usage: audit_bilateral_fronts INPUT OUTPUT
//! OUTPUT is exclusively created JSON. The n=11 fixture is a local topology test.
use anyhow::{ensure, Context, Result};
use grid_graphs::certificate_corpus::{observe, Board};
use serde::Deserialize;
use serde_json::{json, Value};
use std::collections::HashMap;
use std::fs::{File, OpenOptions};
use std::io::{BufReader, BufWriter, Write};

// phase, previous/current masks, six canonical labels, four packed dimer bits.
type State = [usize; 10];
type Edge = (usize, usize, i64, usize, [i64; 13]);

#[derive(Deserialize)]
struct Archive {
    schema: usize,
    status: String,
    exhaustive_graph: bool,
    state_fields: Vec<String>,
    row_bit_order: Vec<String>,
    charge_order: Vec<String>,
    states: Vec<State>,
    initials: Vec<usize>,
    edges: Vec<Edge>,
    potential: Option<Vec<i64>>,
    negative_cycle_edges: Option<Vec<usize>>,
    endpoint_error: Option<i64>,
}

fn f(mask: usize, c: usize) -> bool {
    mask & (1 << c) != 0
}

// Keep EVERY edge occurrence: parallel edges and loops must count as cycles.
// Isolated vertices count as components. No union/find is used anywhere here.
fn components(n: usize, edges: &[(usize, usize)]) -> (bool, Vec<usize>) {
    let mut adjacency = vec![Vec::new(); n];
    for &(u, v) in edges {
        adjacency[u].push(v);
        adjacency[v].push(u);
    }
    let mut labels = vec![usize::MAX; n];
    let mut count = 0;
    for start in 0..n {
        if labels[start] != usize::MAX {
            continue;
        }
        labels[start] = count;
        let mut stack = vec![start];
        while let Some(u) = stack.pop() {
            for &v in &adjacency[u] {
                if labels[v] == usize::MAX {
                    labels[v] = count;
                    stack.push(v);
                }
            }
        }
        count += 1;
    }
    (edges.len() == n - count, labels)
}

fn canonical(labels: &[usize]) -> [usize; 6] {
    let mut names = Vec::new();
    let mut result = [0; 6];
    for (v, &label) in labels.iter().enumerate() {
        result[v] = match names.iter().position(|&x| x == label) {
            Some(i) => i,
            None => {
                names.push(label);
                names.len() - 1
            }
        };
    }
    result
}

fn horizontal(edges: &mut Vec<(usize, usize)>, offset: usize, mask: usize) {
    for c in [0, 1, 3, 4] {
        if f(mask, c) || f(mask, c + 1) {
            edges.push((offset + c, offset + c + 1));
        }
    }
}

fn initial(mask: usize) -> State {
    let mut edges = Vec::new();
    horizontal(&mut edges, 0, mask);
    // Exactly one edge suppresses the entire actual central F path, even if
    // either P is U. There is no persistent root and no previous-row graph.
    edges.push((0, 3));
    let (forest, labels) = components(6, &edges);
    assert!(forest);
    let mut state = [0; 10];
    // Virtual previous S bits only suppress the first singleton on each side.
    state[1] = 18;
    state[2] = mask;
    state[3..9].copy_from_slice(&canonical(&labels));
    state
}

fn charges(state: &State, next: usize) -> ([i64; 13], usize) {
    let (phase, prev, cur) = (state[0], state[1], state[2]);
    let mut flags = state[9];
    let mut terms = [0; 13];
    for side in 0..2 {
        let p = 3 * side;
        let s = p + 1;
        let b = p + 2;
        let t = 6 * side;
        terms[t] = (!f(cur, b)) as i64;
        terms[t + 1] = (f(cur, b) && !f(prev, b) && !f(cur, s)) as i64;
        if phase != 0 {
            // Off-phase P is fixed U; its central neighbour is also U.
            terms[t + 2] = (!f(prev, p) && !f(next, p) && !f(cur, s)) as i64;
            terms[t + 3] = (!f(cur, s) && !f(cur, b) && !f(prev, s) && !f(next, s)) as i64;
            let slot = 1 << (2 * side + phase - 1);
            let dimer = f(cur, s) && f(cur, b);
            terms[t + 5] = (dimer && flags & slot == 0) as i64;
            flags &= !slot;
            if dimer {
                flags |= slot;
            }
        }
        terms[t + 4] = (f(cur, s) && !f(cur, p) && !f(cur, b) && !f(prev, s) && !f(next, s)) as i64;
    }
    terms[12] = (phase != 0) as i64;
    (terms, flags)
}

fn step(state: &State, next: usize) -> Option<(State, i64, [i64; 13])> {
    let phase = (state[0] + 1) % 3;
    if phase != 0 && next & 9 != 0 {
        return None;
    }
    let mut edges = Vec::new();
    // Represent each old component by a star at its last representative.
    // These are connectivity surrogates, not all pairs of equivalent labels.
    for v in 0..6 {
        let centre = (0..6)
            .rev()
            .find(|&w| state[3 + w] == state[3 + v])
            .unwrap();
        if v != centre {
            edges.push((centre, v));
        }
    }
    for c in 0..6 {
        if f(state[2], c) || f(next, c) {
            edges.push((c, 6 + c));
        }
    }
    horizontal(&mut edges, 6, next);
    if phase == 0 {
        edges.push((6, 9));
    }
    let (forest, labels) = components(12, &edges);
    if !forest {
        return None;
    }
    let (terms, flags) = charges(state, next);
    let weight = terms[..12].iter().sum::<i64>() - terms[12];
    let mut target = [0; 10];
    target[..3].copy_from_slice(&[phase, state[2], next]);
    target[3..9].copy_from_slice(&canonical(&labels[6..12]));
    target[9] = flags;
    Some((target, weight, terms))
}

fn intern(state: State, states: &mut Vec<State>, index: &mut HashMap<State, usize>) -> usize {
    if let Some(&i) = index.get(&state) {
        return i;
    }
    let i = states.len();
    states.push(state);
    index.insert(state, i);
    i
}

fn graph() -> (Vec<State>, Vec<usize>, Vec<Edge>) {
    let mut states = Vec::new();
    let mut index = HashMap::new();
    let initials = (0..64)
        .map(|mask| intern(initial(mask), &mut states, &mut index))
        .collect();
    let mut edges = Vec::new();
    let mut u = 0;
    // Ascending masks and FIFO discovery reproduce the complete ordered arrays.
    while u < states.len() {
        for mask in 0..64 {
            if let Some((target, weight, terms)) = step(&states[u], mask) {
                let v = intern(target, &mut states, &mut index);
                edges.push((u, v, weight, mask, terms));
            }
        }
        u += 1;
    }
    (states, initials, edges)
}

fn terminal(state: &State) -> i64 {
    [2, 5]
        .iter()
        .map(|&b| {
            (!f(state[2], b)) as i64
                + (f(state[2], b) && !f(state[1], b) && !f(state[2], b - 1)) as i64
        })
        .sum()
}

// Literal 24-vertex graph, independently enumerated without the frontier's
// horizontal/step helpers or partitions. Rows 0 and 3 each have one PL--PR
// edge standing for their actual central path. Omitted physical edges are
// pendant trees or isolated vertices in this particular fixture.
fn strip_forest(rows: &[usize; 4]) -> bool {
    let mut edges = Vec::new();
    for u in 0..24 {
        for v in u + 1..24 {
            let (r, c) = (u / 6, u % 6);
            let (s, d) = (v / 6, v % 6);
            let adjacent = (r == s && c / 3 == d / 3 && d == c + 1) || (s == r + 1 && c == d);
            if adjacent && (rows[r] & (1 << c) != 0 || rows[s] & (1 << d) != 0) {
                edges.push((u, v));
            }
        }
    }
    edges.extend([(0, 3), (18, 21)]);
    components(24, &edges).0
}

fn physical_check() -> Result<Value> {
    let mut board = Board {
        n: 11,
        preserved: vec![false; 121],
    };
    for y in [3, 6] {
        for x in 3..=7 {
            board.preserved[y * 11 + x] = true;
        }
    }
    // Local bit order reverses the left side: PL,SL,BL,PR,SR,BR.
    let columns = [2, 1, 0, 8, 9, 10];
    let mut variables = Vec::new();
    for y in 3..=6 {
        for x in [0, 1, 2, 8, 9, 10] {
            if (y == 4 || y == 5) && (x == 2 || x == 8) {
                continue;
            }
            variables.push(y * 11 + x);
        }
    }
    ensure!(variables.len() == 20, "physical fixture variable count");
    ensure!(
        board.preserved.iter().filter(|&&x| x).count() == 10,
        "fixed F count"
    );
    let assignments = 1usize << variables.len();
    let mut feasible = 0usize;
    for assignment in 0..assignments {
        for (bit, &v) in variables.iter().enumerate() {
            board.preserved[v] = assignment & (1 << bit) != 0;
        }
        let mut rows = [0; 4];
        for r in 0..4 {
            for (c, &x) in columns.iter().enumerate() {
                rows[r] |= (board.preserved[(r + 3) * 11 + x] as usize) << c;
            }
        }
        let full = match observe(&board) {
            Ok(_) => true,
            Err(e) => {
                ensure!(
                    e == "primal forced graph contains a cycle",
                    "observe failed: {e}"
                );
                false
            }
        };
        let direct = strip_forest(&rows);
        let mut frontier = Some(initial(rows[0]));
        for &next in &rows[1..] {
            frontier = frontier.and_then(|s| step(&s, next).map(|t| t.0));
        }
        ensure!(
            full == direct && direct == frontier.is_some(),
            "physical/strip/frontier mismatch at assignment {assignment}, rows {rows:?}"
        );
        feasible += usize::from(full);
    }
    Ok(json!({
        "scope": "specified n=11 local topology fixture only",
        "n": 11, "A": 10, "block_size": 4,
        "physical_rows": [3,4,5,6], "marked_rows": [3,6],
        "central_fixed_F_columns": [3,4,5,6,7],
        "local_bit_columns": columns, "off_P_fixed_U_rows": [4,5],
        "off_P_fixed_U_columns": [2,8], "all_other_labels": "U",
        "variables": variables.len(), "variable_vertices_row_major": variables,
        "assignments_checked": assignments, "feasible_count": feasible,
        "cyclic_count": assignments - feasible,
        "full_observe_checks": assignments, "direct_strip_checks": assignments,
        "frontier_acceptance_checks": assignments,
        "full_observe_vs_direct_strip_checks": assignments,
        "direct_strip_vs_frontier_checks": assignments,
        "full_observe_vs_frontier_checks": assignments
    }))
}

fn audit(a: &Archive) -> Result<Value> {
    ensure!(
        a.schema == 1 && a.status == "potential" && a.exhaustive_graph,
        "archive header differs"
    );
    ensure!(
        a.state_fields
            == [
                "phase",
                "previous_mask",
                "current_mask",
                "PL",
                "SL",
                "BL",
                "PR",
                "SR",
                "BR",
                "dimer_history"
            ],
        "state fields differ"
    );
    ensure!(
        a.row_bit_order == ["PL", "SL", "BL", "PR", "SR", "BR"],
        "row bit order differs"
    );
    ensure!(
        a.charge_order
            == [
                "hL",
                "pureL",
                "deepL",
                "nearL",
                "singletonL",
                "dimer_startL",
                "hR",
                "pureR",
                "deepR",
                "nearR",
                "singletonR",
                "dimer_startR",
                "demand"
            ],
        "charge order differs"
    );
    let (states, initials, edges) = graph();
    ensure!(
        (states.len(), initials.len(), edges.len()) == (2424, 64, 22508),
        "unexpected batch003 graph counts"
    );
    ensure!(states == a.states, "complete ordered state array differs");
    ensure!(
        initials == a.initials,
        "complete ordered initial array differs"
    );
    ensure!(
        edges == a.edges,
        "complete ordered edge array (including all 13 terms) differs"
    );
    ensure!(
        a.negative_cycle_edges.is_none(),
        "unexpected negative cycle"
    );
    let phi = a.potential.as_ref().context("missing potential")?;
    ensure!(phi.len() == states.len(), "potential length differs");
    let lo = *phi.iter().min().unwrap();
    let hi = *phi.iter().max().unwrap();
    ensure!((lo, hi) == (-3, 0), "unexpected potential range");
    let mut tight = 0usize;
    let mut min_slack = i64::MAX;
    for (i, &(u, v, weight, _, _)) in edges.iter().enumerate() {
        let slack = weight + phi[u] - phi[v];
        ensure!(slack >= 0, "potential inequality fails on edge {i}");
        tight += usize::from(slack == 0);
        min_slack = min_slack.min(slack);
    }
    let initial_max = initials.iter().map(|&i| phi[i]).max().unwrap();
    let terminals: Vec<_> = states
        .iter()
        .enumerate()
        .filter(|(_, s)| s[0] == 0)
        .collect();
    let terminal_min = terminals
        .iter()
        .map(|&(i, s)| phi[i] + terminal(s))
        .min()
        .unwrap();
    let endpoint = (initial_max - terminal_min).max(0);
    ensure!(
        endpoint == 2 && a.endpoint_error == Some(endpoint),
        "endpoint constant differs"
    );
    // Explicitly check the bound for every initial/marked-terminal pair.
    let mut endpoint_checks = 0usize;
    for &start in &initials {
        for &(end, state) in &terminals {
            ensure!(
                phi[start] - phi[end] - terminal(state) <= endpoint,
                "endpoint inequality fails"
            );
            endpoint_checks += 1;
        }
    }
    Ok(json!({
        "schema": 1, "status": "passed", "batch": "batch003",
        "scope": "complete finite bilateral necessary-condition graph and specified n=11 local topology fixture only; no uniform geometric or n>15 claim",
        "method": "explicit adjacency components; old-partition star forest; multiplicity-preserving E=V-components; one marked PL--PR path; no persistent root",
        "states": states.len(), "initials": initials.len(), "edges": edges.len(),
        "candidate_transitions_checked": 64 * states.len(),
        "rejected_transitions": 64 * states.len() - edges.len(),
        "exact_ordered_graph_arrays": true, "integer_weight_checks": edges.len(),
        "integer_term_checks": 13 * edges.len(),
        "certificate": {
            "kind": "integer_potential", "inequalities_checked": edges.len(),
            "potential_min": lo, "potential_max": hi, "tight_edges": tight,
            "minimum_slack": min_slack, "initial_states_checked": initials.len(),
            "initial_max": initial_max, "terminal_states_checked": terminals.len(),
            "terminal_min": terminal_min, "endpoint_error": endpoint,
            "initial_terminal_bound_checks": endpoint_checks
        },
        "physical_check": physical_check()?
    }))
}

fn main() -> Result<()> {
    let args: Vec<_> = std::env::args_os().skip(1).collect();
    ensure!(
        args.len() == 2,
        "usage: audit_bilateral_fronts INPUT OUTPUT"
    );
    let input = File::open(&args[0]).context("open INPUT")?;
    let archive: Archive = serde_json::from_reader(BufReader::new(input)).context("parse INPUT")?;
    // Reserve OUTPUT before graph regeneration or exhaustive physical checks.
    let output = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&args[1])
        .context("create OUTPUT exclusively")?;
    let report = audit(&archive)?;
    let mut writer = BufWriter::new(output);
    serde_json::to_writer_pretty(&mut writer, &report)?;
    writer.write_all(b"\n")?;
    writer.flush()?;
    Ok(())
}
