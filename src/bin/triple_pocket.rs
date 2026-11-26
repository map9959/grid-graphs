//! SAT over fully free repeat cells. Enforce quotient pseudoforest by
//! orientation, then separate actual contractible cycles by their winding.
use serde::Deserialize;
use serde_json::json;
use std::io::{self, Read};
use varisat::{ExtendFormula, Lit, Solver};

#[derive(Deserialize)]
struct Input {
    n: usize,
    sites: usize,
    target: usize,
    #[serde(default)]
    forbid: Vec<Vec<usize>>,
    edges: Vec<(usize, usize, i32, Vec<usize>)>,
}

fn small_cycles(d: &Input, sol: &mut Solver, es: &[Lit]) -> usize {
    let mut adj = vec![vec![]; d.n];
    for (i, (u, v, w, _)) in d.edges.iter().enumerate() {
        adj[*u].push((*v, *w, i));
        adj[*v].push((*u, -*w, i));
    }
    struct Walk<'a> {
        adj: &'a [Vec<(usize, i32, usize)>],
        es: &'a [Lit],
        n: usize,
    }
    impl Walk<'_> {
        fn walk(
            &mut self,
            sol: &mut Solver,
            s: usize,
            u: usize,
            w: i32,
            path: &mut Vec<usize>,
            visited: &mut [bool],
        ) {
            for &(v, x, e) in &self.adj[u] {
                if v < s || path.contains(&e) {
                    continue;
                }
                if v == s {
                    if w + x == 0 && (path.is_empty() || path[0] < e) {
                        let mut cl = vec![!self.es[e]];
                        cl.extend(path.iter().map(|&i| !self.es[i]));
                        sol.add_clause(&cl);
                        self.n += 1;
                    }
                } else if !visited[v] && path.len() < 5 {
                    path.push(e);
                    visited[v] = true;
                    self.walk(sol, s, v, w + x, path, visited);
                    path.pop();
                    visited[v] = false;
                }
            }
        }
    }
    let mut g = Walk {
        adj: &adj,
        es,
        n: 0,
    };
    let mut visited = vec![false; d.n];
    for s in 0..d.n {
        g.walk(sol, s, s, 0, &mut vec![], &mut visited);
    }
    g.n
}
fn bad_cycle(d: &Input, chosen: &[bool]) -> Option<Vec<usize>> {
    let mut adj = vec![vec![]; d.n];
    for (id, (u, v, w, _)) in d.edges.iter().enumerate() {
        if chosen[id] {
            adj[*u].push((*v, *w, id));
            adj[*v].push((*u, -*w, id));
        }
    }
    let mut height = vec![None; d.n];
    let mut par = vec![None; d.n];
    let mut tree = vec![false; chosen.len()];
    for s in 0..d.n {
        if height[s].is_some() {
            continue;
        }
        height[s] = Some(0);
        let mut stack = vec![s];
        let mut comp = vec![];
        while let Some(u) = stack.pop() {
            comp.push(u);
            for &(v, w, id) in &adj[u] {
                if height[v].is_none() {
                    height[v] = Some(height[u].unwrap() + w);
                    par[v] = Some((u, id));
                    tree[id] = true;
                    stack.push(v);
                }
            }
        }
        let mut nontree = vec![];
        for &u in &comp {
            for &(v, w, id) in &adj[u] {
                if tree[id] || nontree.contains(&id) {
                    continue;
                }
                nontree.push(id);
                if height[u].unwrap() + w == height[v].unwrap() {
                    let mut a = u;
                    let mut b = v;
                    let mut path = vec![id];
                    let mut other = vec![];
                    while let Some((p, e)) = par[a] {
                        path.push(e);
                        a = p;
                    }
                    while let Some((p, e)) = par[b] {
                        other.push(e);
                        b = p;
                    }
                    while path.len() > 1 && !other.is_empty() && path.last() == other.last() {
                        path.pop();
                        other.pop();
                    }
                    path.extend(other);
                    return Some(path);
                }
            }
        }
        assert!(nontree.len() <= 1, "orientation failed");
    }
    None
}
fn main() {
    let mut s = String::new();
    io::stdin().read_to_string(&mut s).unwrap();
    let d: Input = serde_json::from_str(&s).unwrap();
    let mut sol = Solver::new();
    let centers: Vec<Lit> = (0..d.sites).map(|_| sol.new_lit()).collect();
    for pair in &d.forbid {
        sol.add_clause(&pair.iter().map(|&i|!centers[i]).collect::<Vec<_>>());
    }
    let mut outs = vec![vec![]; d.n];
    let mut edges = vec![];
    for (u, v, _, cs) in &d.edges {
        let e = sol.new_lit();
        let a = sol.new_lit();
        let b = sol.new_lit();
        edges.push(e);
        if cs.is_empty() {
            sol.add_clause(&[e]);
        } else {
            let mut cl = vec![!e];
            for &c in cs {
                sol.add_clause(&[!centers[c], e]);
                cl.push(centers[c]);
            }
            sol.add_clause(&cl);
        }
        sol.add_clause(&[!e, a, b]);
        outs[*u].push(a);
        outs[*v].push(b);
    }
    for ls in outs {
        for (i, &l) in ls.iter().enumerate() {
            for &k in &ls[..i] {
                sol.add_clause(&[!k, !l]);
            }
        }
    }
    let _ = small_cycles(&d, &mut sol, &edges);
    // At least target: exact unary recurrence.
    let mut prev: Vec<Lit> = vec![];
    for &c in &centers {
        let mut next = vec![];
        for i in 0..d.target.min(prev.len() + 1) {
            let y = sol.new_lit();
            let x = prev.get(i).copied();
            let t = i.checked_sub(1).map(|j| prev[j]);
            if let Some(x) = x {
                sol.add_clause(&[!x, y]);
            }
            let mut cl = vec![!c, y];
            if let Some(t) = t {
                cl.push(!t)
            }
            sol.add_clause(&cl);
            let mut cl = vec![!y, c];
            if let Some(x) = x {
                cl.push(x)
            }
            sol.add_clause(&cl);
            if let Some(t) = t {
                let mut cl = vec![!y, t];
                if let Some(x) = x {
                    cl.push(x)
                }
                sol.add_clause(&cl);
            }
            next.push(y)
        }
        prev = next;
    }
    sol.add_clause(&[prev[d.target - 1]]);
    let mut cuts = 0;
    loop {
        if !sol.solve().unwrap() {
            println!("{}", json!({"status":"unsat","cuts":cuts}));
            break;
        }
        let model = sol.model().unwrap();
        let values: Vec<_> = edges.iter().map(|e| model.contains(e)).collect();
        if let Some(cycle) = bad_cycle(&d, &values) {
            sol.add_clause(&cycle.into_iter().map(|id| !edges[id]).collect::<Vec<_>>());
            cuts += 1;
        } else {
            let selected: Vec<_> = (0..centers.len())
                .filter(|&i| model.contains(&centers[i]))
                .collect();
            println!(
                "{}",
                json!({"status":"sat","cuts":cuts,"selected":selected})
            );
            break;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn translated_parallel_attachments() {
        // The same pair of root names does not imply the same physical
        // attachment. Equal displacements close a finite two-edge cycle;
        // unequal displacements give a path through successive copies.
        for (a, b, cyclic) in [(0, 0, true), (1, 1, true), (0, 1, false), (-1, 1, false)] {
            let g = Input {
                n: 2,
                sites: 0,
                target: 0,
                forbid: vec![],
                edges: vec![(0, 1, a, vec![]), (0, 1, b, vec![])],
            };
            assert_eq!(bad_cycle(&g, &[true, true]).is_some(), cyclic);
        }
    }
}
