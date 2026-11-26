//! Dedicated bounded-instance SAT backend. Run through the Python outer cap.
//! Every edge variable is F[u] OR F[v] in the supplied Python formula.
//! A rejected model supplies one actual full-primal cycle C; add OR_{e in C} !e.
//! These cuts exclude no forest. UNSAT is scoped to the supplied frozen core
//! and threshold; a round limit or external kill is never an UNSAT result.

use serde::Deserialize;
use serde_json::json;
use std::collections::VecDeque;
use std::io::{self, Read, Write};
use varisat::{ExtendFormula, Lit, Solver};

#[derive(Deserialize)]
struct Request {
    n: usize,
    variables: usize,
    clauses: Vec<Vec<i64>>,
    center_vars: Vec<usize>,
    edges: Vec<[usize; 2]>,
    edge_vars: Vec<usize>,
    max_rounds: usize,
    threshold: usize,
}

fn root(parent: &mut [usize], mut v: usize) -> usize {
    while parent[v] != v {
        parent[v] = parent[parent[v]];
        v = parent[v];
    }
    v
}

/// First rejected union plus its unique path in the previously accepted forest.
fn actual_cycle(n: usize, edges: &[[usize; 2]], centers: &[bool]) -> Option<Vec<usize>> {
    let mut parent: Vec<_> = (0..n * n).collect();
    let mut tree = vec![Vec::<(usize, usize)>::new(); n * n];
    for (index, &[u, v]) in edges.iter().enumerate() {
        if !centers[u] && !centers[v] {
            continue;
        }
        let a = root(&mut parent, u);
        let b = root(&mut parent, v);
        if a != b {
            parent[a] = b;
            tree[u].push((v, index));
            tree[v].push((u, index));
            continue;
        }
        let mut previous = vec![None; n * n];
        previous[u] = Some((u, usize::MAX));
        let mut queue = VecDeque::from([u]);
        while let Some(w) = queue.pop_front() {
            if w == v {
                break;
            }
            for &(next, edge) in &tree[w] {
                if previous[next].is_none() {
                    previous[next] = Some((w, edge));
                    queue.push_back(next);
                }
            }
        }
        let mut cycle = vec![index];
        let mut w = v;
        while w != u {
            let (next, edge) = previous[w].expect("union-find path must exist");
            cycle.push(edge);
            w = next;
        }
        return Some(cycle);
    }
    None
}

fn emit(value: serde_json::Value) -> io::Result<()> {
    let mut out = io::stdout().lock();
    serde_json::to_writer(&mut out, &value)?;
    writeln!(out)?;
    out.flush()
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input)?;
    let request: Request = serde_json::from_str(&input)?;
    if ![8, 14].contains(&request.n)
        || !(1..=10000).contains(&request.max_rounds)
        || request.variables > 100000
        || request.center_vars.len() != request.n * request.n
        || request.edge_vars.len() != request.edges.len()
    {
        return Err("invalid bounded request".into());
    }
    // Require the complete canonical ambient grid, not an induced annulus graph.
    let mut expected = Vec::new();
    for r in 0..request.n {
        for c in 0..request.n {
            let u = r * request.n + c;
            if r + 1 < request.n {
                expected.push([u, u + request.n]);
            }
            if c + 1 < request.n {
                expected.push([u, u + 1]);
            }
        }
    }
    if request.edges != expected {
        return Err("ambient edge list mismatch".into());
    }
    let mut solver = Solver::new();
    let vars: Vec<Lit> = (0..request.variables).map(|_| solver.new_lit()).collect();
    for &id in request.center_vars.iter().chain(request.edge_vars.iter()) {
        if id == 0 || id > vars.len() {
            return Err("invalid variable id".into());
        }
    }
    for clause in &request.clauses {
        let mut lits = Vec::new();
        for &signed in clause {
            if signed == 0 || signed.unsigned_abs() > vars.len() as u64 {
                return Err("invalid clause literal".into());
            }
            let lit = vars[signed.unsigned_abs() as usize - 1];
            lits.push(if signed > 0 { lit } else { !lit });
        }
        solver.add_clause(&lits);
    }
    emit(json!({"event": "ready", "n": request.n, "threshold": request.threshold}))?;
    for round in 0..request.max_rounds {
        if !solver.solve()? {
            emit(json!({"event": "unsat", "round": round}))?;
            return Ok(());
        }
        let mut values = vec![false; vars.len()];
        for lit in solver.model().ok_or("missing SAT model")? {
            values[lit.var().index()] = lit.is_positive();
        }
        let centers: Vec<bool> = request.center_vars.iter().map(|&x| values[x - 1]).collect();
        let ids: Vec<usize> = (0..centers.len()).filter(|&v| centers[v]).collect();
        if ids.len() < request.threshold {
            return Err("threshold encoding/model mismatch".into());
        }
        for (&[u, v], &edge_var) in request.edges.iter().zip(&request.edge_vars) {
            if values[edge_var - 1] != (centers[u] || centers[v]) {
                return Err("edge equivalence/model mismatch".into());
            }
        }
        match actual_cycle(request.n, &request.edges, &centers) {
            None => {
                emit(json!({"event": "sat", "round": round, "centers": ids}))?;
                return Ok(());
            }
            Some(cycle) => {
                let clause: Vec<Lit> = cycle
                    .iter()
                    .map(|&e| !vars[request.edge_vars[e] - 1])
                    .collect();
                solver.add_clause(&clause);
                emit(json!({"event": "cut", "round": round, "centers": ids,
                            "cycle_edge_indices": cycle}))?;
            }
        }
    }
    emit(json!({"event": "round_limit", "rounds": request.max_rounds}))?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::actual_cycle;

    #[test]
    fn extracts_an_actual_cycle_and_accepts_a_tree() {
        let edges = [[0, 1], [1, 9], [9, 8], [8, 0], [9, 10]];
        let mut centers = vec![false; 64];
        centers[0] = true;
        centers[9] = true;
        let cycle = actual_cycle(8, &edges, &centers).unwrap();
        assert_eq!(cycle.len(), 4);
        let mut degree = [0; 64];
        for index in cycle {
            let [u, v] = edges[index];
            assert!(centers[u] || centers[v]);
            degree[u] += 1;
            degree[v] += 1;
        }
        assert!(degree.iter().all(|&d| d == 0 || d == 2));
        centers[9] = false;
        assert!(actual_cycle(8, &edges, &centers).is_none());
    }
}
