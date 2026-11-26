//! Independent finite-graph audit. Usage: audit_mixed_fronts INPUT OUTPUT
//! OUTPUT is created exclusively. No optimization/search or Python invocation.
use anyhow::{ensure, Context, Result};
use grid_graphs::certificate_corpus::{observe, Board};
use serde::Deserialize;
use serde_json::{json, Value};
use std::collections::HashMap;
use std::fs::{File, OpenOptions};
use std::io::{BufReader, BufWriter, Write};

type State = Vec<usize>;
type Edge = (usize, usize, i64, usize, Vec<i64>);

#[derive(Deserialize)]
struct Archive {
    schema: usize,
    #[serde(default)]
    suppliers: bool,
    states: Vec<State>,
    initials: Vec<usize>,
    edges: Vec<Edge>,
    potential: Option<Vec<i64>>,
    negative_cycle_edges: Option<Vec<usize>>,
    endpoint_error: Option<i64>,
}

fn f(mask: usize, column: usize) -> bool {
    mask & (1 << column) != 0
}

// Each edge occurrence is retained, including parallel edges. Component labels
// come from explicit adjacency traversal, never union/find. For an undirected
// multigraph (including isolated vertices), forest iff E = V - components.
fn components(n: usize, edges: &[(usize, usize)]) -> (bool, Vec<usize>) {
    let mut adjacency = vec![Vec::new(); n];
    for &(a, b) in edges {
        adjacency[a].push(b);
        adjacency[b].push(a);
    }
    let mut labels = vec![usize::MAX; n];
    let mut count = 0;
    for start in 0..n {
        if labels[start] != usize::MAX {
            continue;
        }
        labels[start] = count;
        let mut stack = vec![start];
        while let Some(v) = stack.pop() {
            for &w in &adjacency[v] {
                if labels[w] == usize::MAX {
                    labels[w] = count;
                    stack.push(w);
                }
            }
        }
        count += 1;
    }
    (edges.len() == n - count, labels)
}

fn canonical(labels: &[usize], frontier: &[usize]) -> Vec<usize> {
    let mut names = Vec::new();
    frontier
        .iter()
        .map(|&v| {
            let label = labels[v];
            if let Some(i) = names.iter().position(|&x| x == label) {
                i
            } else {
                names.push(label);
                names.len() - 1
            }
        })
        .collect()
}

fn horizontal(edges: &mut Vec<(usize, usize)>, base: usize, mask: usize) {
    for c in 0..2 {
        if f(mask, c) || f(mask, c + 1) {
            edges.push((base + c, base + c + 1));
        }
    }
}

fn initial(mask: usize, suppliers: bool) -> State {
    let mut edges = vec![(0, 3)]; // Actual marked back-root edge, even P=U.
    horizontal(&mut edges, 0, mask);
    let (forest, labels) = components(4, &edges);
    assert!(forest);
    // Virtual previous S=F affects only the unsupported first singleton:
    // phase=0 has no off-isolates/demand, and boundary previous bit stays U.
    let mut state = vec![0, if suppliers { 2 } else { 0 }, mask];
    state.extend(canonical(&labels, &[0, 1, 2, 3]));
    if suppliers {
        state.push(0);
    }
    state
}

// Finalize actual current-row labels with both neighbouring rows present.
fn charges(state: &[usize], next: usize, suppliers: bool) -> (Vec<i64>, usize) {
    let (phase, prev, cur) = (state[0], state[1], state[2]);
    let p = f(cur, 0);
    let s = f(cur, 1);
    let b = f(cur, 2);
    let off = phase != 0;
    let hole = !b;
    let pure_run_start = b && !f(prev, 2) && !s;
    // Off P is U; its other horizontal neighbour (back q) is U.
    let deep_isolate = off && !p && !s && !f(prev, 0) && !f(next, 0);
    let near_isolate = off && !s && !p && !b && !f(prev, 1) && !f(next, 1);
    let mut terms = vec![
        hole as i64,
        pure_run_start as i64,
        deep_isolate as i64,
        near_isolate as i64,
        off as i64,
    ];
    let mut memory = if suppliers { state[7] } else { 0 };
    if suppliers {
        let singleton = s && !p && !b && !f(prev, 1) && !f(next, 1);
        let mut chain_start = false;
        if off {
            // Remember the preceding row of THIS off-phase (three rows ago),
            // not the immediately preceding row. Charge once per dimer chain.
            let slot = 1 << (phase - 1);
            let dimer = s && b;
            chain_start = dimer && memory & slot == 0;
            memory &= !slot;
            if dimer {
                memory |= slot;
            }
        }
        terms.extend([singleton as i64, chain_start as i64]);
    }
    (terms, memory)
}

fn step(state: &[usize], next: usize, suppliers: bool) -> Option<(State, i64, Vec<i64>)> {
    let phase = (state[0] + 1) % 3;
    if phase != 0 && f(next, 0) {
        return None;
    }
    let mut edges = Vec::new();
    // Replace each old component by an arbitrary star centred at its LAST
    // frontier representative. Only connectivity survives forgotten vertices.
    for v in 0..4 {
        let centre = (0..4)
            .rev()
            .find(|&w| state[3 + w] == state[3 + v])
            .unwrap();
        if v != centre {
            edges.push((centre, v));
        }
    }
    for c in 0..3 {
        if f(state[2], c) || f(next, c) {
            edges.push((c, 4 + c));
        }
    }
    horizontal(&mut edges, 4, next);
    if phase == 0 {
        edges.push((3, 4));
    }
    let (forest, labels) = components(7, &edges);
    if !forest {
        return None;
    }
    let (terms, memory) = charges(state, next, suppliers);
    let weight = terms.iter().sum::<i64>() - 2 * terms[4];
    let mut target = vec![phase, state[2], next];
    target.extend(canonical(&labels, &[4, 5, 6, 3]));
    if suppliers {
        target.push(memory);
    }
    Some((target, weight, terms))
}

fn intern(state: State, states: &mut Vec<State>, index: &mut HashMap<State, usize>) -> usize {
    if let Some(&i) = index.get(&state) {
        return i;
    }
    let i = states.len();
    index.insert(state.clone(), i);
    states.push(state);
    i
}

fn graph(suppliers: bool) -> (Vec<State>, Vec<usize>, Vec<Edge>) {
    let mut states = Vec::new();
    let mut index = HashMap::new();
    let initials = (0..8)
        .map(|mask| intern(initial(mask, suppliers), &mut states, &mut index))
        .collect();
    let mut edges = Vec::new();
    let mut u = 0;
    // Growing array is a FIFO worklist. Every reachable state, every next mask.
    while u < states.len() {
        for mask in 0..8 {
            if let Some((target, weight, terms)) = step(&states[u], mask, suppliers) {
                let v = intern(target, &mut states, &mut index);
                edges.push((u, v, weight, mask, terms));
            }
        }
        u += 1;
    }
    (states, initials, edges)
}

fn terminal(state: &[usize]) -> i64 {
    let (prev, cur) = (state[1], state[2]);
    (!f(cur, 2)) as i64 + (f(cur, 2) && !f(prev, 2) && !f(cur, 1)) as i64
}

// Literal 7-row, three-column graph with one common back root. This does not
// use frontier partitions. Outside-strip edges of the specified physical board
// are in the back tree or pendant trees and cannot create additional cycles.
fn strip_forest(rows: &[usize; 7]) -> bool {
    let mut edges = Vec::new();
    for r in 0..7 {
        horizontal(&mut edges, 3 * r, rows[r]);
        if r % 3 == 0 {
            edges.push((21, 3 * r));
        }
        if r > 0 {
            for c in 0..3 {
                if f(rows[r - 1], c) || f(rows[r], c) {
                    edges.push((3 * (r - 1) + c, 3 * r + c));
                }
            }
        }
    }
    components(22, &edges).0
}

fn physical_check(suppliers: bool) -> Result<Value> {
    let mut board = Board {
        n: 11,
        preserved: vec![false; 121],
    };
    for y in 0..11 {
        board.preserved[y * 11] = true;
    }
    let mut variables = Vec::new();
    for y in [2, 5, 8] {
        for x in 2..=7 {
            board.preserved[y * 11 + x] = true;
        }
        variables.push(y * 11 + 8);
    }
    for y in 2..=8 {
        for x in 9..=10 {
            variables.push(y * 11 + x);
        }
    }
    ensure!(variables.len() == 17, "physical fixture variable count");
    let mut forests = 0usize;
    for mask in 0usize..(1 << 17) {
        for (bit, &v) in variables.iter().enumerate() {
            board.preserved[v] = mask & (1 << bit) != 0;
        }
        let mut rows = [0usize; 7];
        for r in 0..7 {
            for c in 0..3 {
                rows[r] |= (board.preserved[(r + 2) * 11 + c + 8] as usize) << c;
            }
        }
        let direct = strip_forest(&rows);
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
        let mut frontier = Some(initial(rows[0], suppliers));
        for &next in &rows[1..] {
            frontier = frontier.and_then(|s| step(&s, next, suppliers).map(|t| t.0));
        }
        ensure!(
            full == direct && direct == frontier.is_some(),
            "physical/strip/frontier mismatch at assignment {mask}"
        );
        forests += usize::from(full);
    }
    Ok(json!({"n": 11, "rows": 7, "variables": 17,
        "assignments_checked": 131072, "forest_assignments": forests,
        "cyclic_assignments": 131072 - forests,
        "full_observe_vs_direct_strip_checks": 131072,
        "direct_strip_vs_frontier_checks": 131072}))
}

fn audit(a: &Archive) -> Result<Value> {
    ensure!(a.schema == 1, "unsupported schema");
    let (states, initials, edges) = graph(a.suppliers);
    ensure!(states == a.states, "complete ordered state array differs");
    ensure!(initials == a.initials, "ordered initial array differs");
    ensure!(
        edges == a.edges,
        "complete ordered edge array (including terms) differs"
    );
    let expected = if a.suppliers { (104, 300) } else { (59, 171) };
    ensure!(
        (states.len(), edges.len()) == expected,
        "unexpected batch002 counts"
    );
    let certificate = if a.suppliers {
        ensure!(
            a.negative_cycle_edges.is_none(),
            "unexpected negative cycle"
        );
        let phi = a.potential.as_ref().context("missing potential")?;
        ensure!(phi.len() == states.len(), "potential length differs");
        let lo = *phi.iter().min().unwrap();
        let hi = *phi.iter().max().unwrap();
        ensure!((lo, hi) == (-3, 0), "unexpected potential range");
        let mut tight = 0;
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
        json!({"kind": "integer_potential", "inequalities_checked": edges.len(),
            "potential_min": lo, "potential_max": hi, "tight_edges": tight,
            "minimum_slack": min_slack, "initial_max": initial_max,
            "terminal_states_checked": terminals.len(), "terminal_min": terminal_min,
            "endpoint_error": endpoint})
    } else {
        ensure!(a.potential.is_none(), "unexpected old-model potential");
        let cycle = a
            .negative_cycle_edges
            .as_ref()
            .context("missing negative cycle")?;
        ensure!(!cycle.is_empty(), "empty negative cycle");
        let mut weight = 0i64;
        for (k, &i) in cycle.iter().enumerate() {
            let edge = edges.get(i).context("cycle edge index out of range")?;
            let next = edges
                .get(cycle[(k + 1) % cycle.len()])
                .context("cycle edge index out of range")?;
            ensure!(edge.1 == next.0, "cycle disconnected at position {k}");
            weight += edge.2;
        }
        ensure!(weight < 0, "cycle weight is not negative");
        json!({"kind": "negative_cycle", "edge_indices": cycle,
            "edge_membership_checks": cycle.len(), "connection_checks_including_closure": cycle.len(),
            "total_weight": weight})
    };
    Ok(
        json!({"schema": 1, "status": "passed", "suppliers": a.suppliers,
        "scope": "finite reachable rooted relaxation and specified n=11 fixture only; no uniform geometric soundness or supplier nonreuse proof",
        "method": "explicit adjacency traversal; old-component stars; multiplicity-preserving E=V-components",
        "states": states.len(), "initials": initials.len(), "edges": edges.len(),
        "candidate_transitions_checked": 8 * states.len(),
        "rejected_transitions": 8 * states.len() - edges.len(),
        "exact_ordered_graph_arrays": true, "integer_weight_checks": edges.len(),
        "integer_term_checks": edges.len() * if a.suppliers { 7 } else { 5 },
        "certificate": certificate, "physical_check": physical_check(a.suppliers)?}),
    )
}

fn main() -> Result<()> {
    let args: Vec<_> = std::env::args_os().skip(1).collect();
    ensure!(args.len() == 2, "usage: audit_mixed_fronts INPUT OUTPUT");
    let input = File::open(&args[0]).context("open INPUT")?;
    let archive: Archive = serde_json::from_reader(BufReader::new(input)).context("parse INPUT")?;
    // Reserve exclusively before any potentially expensive audit work.
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
    println!(
        "audit passed: {} states, {} edges; 131072 physical assignments checked",
        archive.states.len(),
        archive.edges.len()
    );
    Ok(())
}
