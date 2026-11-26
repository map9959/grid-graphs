//! Independent four-for-five audit using literal graph traversal, not the
//! incremental DSU, its insertion routine, or the deletion-search enumerator.
use anyhow::{anyhow, bail, Result};
use grid_graphs::certificate_corpus::{observe, Board};
use serde_json::{json, Value};
use std::{
    collections::BTreeMap,
    env, fs,
    time::{Duration, Instant},
};

struct Grid {
    neighbors: Vec<Vec<usize>>,
}
impl Grid {
    fn new(n: usize) -> Self {
        let mut neighbors = vec![Vec::new(); n * n];
        for y in 0..n {
            for x in 0..n {
                let a = y * n + x;
                if x + 1 < n {
                    neighbors[a].push(a + 1);
                    neighbors[a + 1].push(a);
                }
                if y + 1 < n {
                    neighbors[a].push(a + n);
                    neighbors[a + n].push(a);
                }
            }
        }
        Self { neighbors }
    }
    fn graph(&self, f: &[bool]) -> ([usize; 225], usize, usize) {
        let mut labels = [usize::MAX; 225];
        let mut queue = [0; 225];
        let (mut components, mut degree_sum) = (0, 0);
        for start in 0..f.len() {
            if labels[start] != usize::MAX {
                continue;
            }
            labels[start] = components;
            queue[0] = start;
            let (mut first, mut last) = (0, 1);
            while first < last {
                let v = queue[first];
                first += 1;
                for &w in &self.neighbors[v] {
                    if !(f[v] || f[w]) {
                        continue;
                    }
                    degree_sum += 1;
                    if labels[w] == usize::MAX {
                        labels[w] = components;
                        queue[last] = w;
                        last += 1;
                    }
                }
            }
            components += 1;
        }
        (labels, components, degree_sum / 2)
    }
}

fn audit(b: &Board, node_limit: u64, milliseconds: u64) -> Result<Value> {
    if !(1..=15).contains(&b.n) {
        bail!("audit restricted to side 1..=15");
    }
    let original = observe(b).map_err(|e| anyhow!(e))?;
    let grid = Grid::new(b.n);
    let selected: Vec<_> = (0..b.preserved.len()).filter(|&v| b.preserved[v]).collect();
    let holes: Vec<_> = (0..b.preserved.len())
        .filter(|&v| !b.preserved[v])
        .collect();
    let total = if selected.len() < 4 {
        0
    } else {
        selected.len() * (selected.len() - 1) * (selected.len() - 2) * (selected.len() - 3) / 24
    };
    let started = Instant::now();
    let duration = Duration::from_millis(milliseconds);
    let (mut nodes, mut sets_started, mut sets_completed, mut subsets_checked) =
        (0u64, 0usize, 0usize, 0usize);
    let mut histogram = BTreeMap::<usize, usize>::new();
    macro_rules! finish {
        ($status:expr, $witness:expr) => {
            json!({"schema": "grid-graphs.literal-four-for-five-audit.v1",
                "scope": "fixed input four-for-five neighborhood only; independent of DSU search",
                "n": b.n, "original_f": original.features["f"], "status": $status,
                "node_limit": node_limit, "time_limit_ms": milliseconds, "nodes": nodes,
                "total_deletion_sets": total, "deletion_sets_started": sets_started,
                "deletion_sets_completed": sets_completed, "five_subsets_checked": subsets_checked,
                "initially_legal_hole_histogram": histogram,
                "elapsed_seconds": started.elapsed().as_secs_f64(), "improvement": $witness})
        }
    }
    macro_rules! tick {
        () => {
            if nodes >= node_limit {
                return Ok(finish!("node_limit", Value::Null));
            }
            if started.elapsed() >= duration {
                return Ok(finish!("time_limit", Value::Null));
            }
            nodes += 1;
        };
    }
    // Four explicit loops, independent of the production combination cursor.
    for i in 0..selected.len() {
        for j in i + 1..selected.len() {
            for k in j + 1..selected.len() {
                for l in k + 1..selected.len() {
                    tick!();
                    sets_started += 1;
                    let deleted = [selected[i], selected[j], selected[k], selected[l]];
                    let mut f = b.preserved.clone();
                    for &v in &deleted {
                        f[v] = false;
                    }
                    let (labels, components, edges) = grid.graph(&f);
                    if edges + components != f.len() {
                        bail!("deletion of a forest produced a cycle");
                    }
                    let mut candidates = Vec::new();
                    for &v in &holes {
                        tick!();
                        let mut terminals = vec![labels[v]];
                        for &w in &grid.neighbors[v] {
                            if !f[w] {
                                terminals.push(labels[w]);
                            }
                        }
                        let count = terminals.len();
                        terminals.sort_unstable();
                        terminals.dedup();
                        if count == terminals.len() {
                            candidates.push(v);
                        }
                    }
                    *histogram.entry(candidates.len()).or_default() += 1;
                    // No incremental prefix pruning here: test every five-subset of
                    // individually legal candidates by rebuilding the whole graph.
                    for a in 0..candidates.len() {
                        for c in a + 1..candidates.len() {
                            for d in c + 1..candidates.len() {
                                for e in d + 1..candidates.len() {
                                    for g in e + 1..candidates.len() {
                                        tick!();
                                        subsets_checked += 1;
                                        let added = [
                                            candidates[a],
                                            candidates[c],
                                            candidates[d],
                                            candidates[e],
                                            candidates[g],
                                        ];
                                        for &v in &added {
                                            f[v] = true;
                                        }
                                        let (_, final_components, final_edges) = grid.graph(&f);
                                        if final_edges + final_components == f.len() {
                                            let witness = observe(&Board {
                                                n: b.n,
                                                preserved: f.clone(),
                                            })
                                            .map_err(|e| anyhow!(e))?;
                                            return Ok(finish!(
                                                "improving_exchange_found",
                                                json!({"deleted": deleted,
                                "added": added, "witness": witness})
                                            ));
                                        }
                                        for &v in &added {
                                            f[v] = false;
                                        }
                                    }
                                }
                            }
                        }
                    }
                    sets_completed += 1;
                }
            }
        }
    }
    Ok(finish!("exhausted_neighborhood", Value::Null))
}

fn main() -> Result<()> {
    let args: Vec<_> = env::args().skip(1).collect();
    if args.len() != 3 {
        bail!("usage: audit_deletion_four U_WITNESS MAX_NODES MAX_MILLISECONDS");
    }
    let b = Board::parse(&fs::read_to_string(&args[0])?).map_err(|e| anyhow!(e))?;
    let result = audit(&b, args[1].parse()?, args[2].parse()?)?;
    serde_json::to_writer_pretty(std::io::stdout().lock(), &result)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn graph_traversal_matches_all_four_square_subsets() {
        let grid = Grid::new(4);
        for mask in 0u32..1 << 16 {
            let b = Board {
                n: 4,
                preserved: (0..16).map(|v| mask & (1 << v) != 0).collect(),
            };
            let (_, c, e) = grid.graph(&b.preserved);
            assert_eq!(c + e == 16, observe(&b).is_ok(), "mask={mask:x}");
        }
    }
    #[test]
    fn positive_negative_and_partial_audits() {
        let top = Board::parse("....\nUUUU\nUUUU\nUUUU").unwrap();
        assert_eq!(
            audit(&top, 10000, 60000).unwrap()["status"],
            "improving_exchange_found"
        );
        let maximal = Board::parse("....\nUUUU\nUUUU\n....").unwrap();
        let result = audit(&maximal, 10000, 60000).unwrap();
        assert_eq!(result["status"], "exhausted_neighborhood");
        assert_eq!(result["deletion_sets_completed"], 70);
        assert_eq!(audit(&top, 1, 60000).unwrap()["status"], "node_limit");
        assert_eq!(audit(&top, 100, 0).unwrap()["status"], "time_limit");
    }
}
