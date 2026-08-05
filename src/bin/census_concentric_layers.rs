//! Exact dual-rank census for selected concentric layer-count optima.

use std::collections::BTreeMap;
use std::env;
use std::fs;
use std::path::PathBuf;

use serde_json::{json, Value};

#[derive(Clone, Copy)]
struct DualEdge {
    primal_mask: u64,
    left: usize,
    right: usize,
}

struct Dsu {
    parent: Vec<usize>,
}

impl Dsu {
    fn new(size: usize) -> Self {
        Self {
            parent: (0..size).collect(),
        }
    }

    fn find(&mut self, value: usize) -> usize {
        let parent = self.parent[value];
        if parent != value {
            self.parent[value] = self.find(parent);
        }
        self.parent[value]
    }

    fn union(&mut self, left: usize, right: usize) -> bool {
        let left = self.find(left);
        let right = self.find(right);
        if left == right {
            return false;
        }
        self.parent[right] = left;
        true
    }
}

fn face(n: usize, row: usize, column: usize) -> usize {
    1 + row * (n - 1) + column
}

fn dual_edges(n: usize) -> Vec<DualEdge> {
    let mut edges = Vec::new();
    for row in 0..n {
        for column in 0..n - 1 {
            edges.push(DualEdge {
                primal_mask: (1 << (row * n + column)) | (1 << (row * n + column + 1)),
                left: if row == 0 {
                    0
                } else {
                    face(n, row - 1, column)
                },
                right: if row + 1 == n {
                    0
                } else {
                    face(n, row, column)
                },
            });
        }
    }
    for row in 0..n - 1 {
        for column in 0..n {
            edges.push(DualEdge {
                primal_mask: (1 << (row * n + column)) | (1 << ((row + 1) * n + column)),
                left: if column == 0 {
                    0
                } else {
                    face(n, row, column - 1)
                },
                right: if column + 1 == n {
                    0
                } else {
                    face(n, row, column)
                },
            });
        }
    }
    edges
}

fn boundary(n: usize, offset: usize) -> Vec<usize> {
    let low = offset;
    let high = n - 1 - offset;
    (low..=high)
        .flat_map(|row| {
            (low..=high).filter_map(move |column| {
                (row == low || row == high || column == low || column == high)
                    .then_some(row * n + column)
            })
        })
        .collect()
}

fn corners(n: usize, offset: usize) -> Vec<usize> {
    let low = offset;
    let high = n - 1 - offset;
    vec![
        low * n + low,
        low * n + high,
        high * n + low,
        high * n + high,
    ]
}

fn combination_masks(values: &[usize], choose: usize) -> Vec<u64> {
    fn visit(values: &[usize], choose: usize, at: usize, mask: u64, output: &mut Vec<u64>) {
        if choose == 0 {
            output.push(mask);
            return;
        }
        if values.len() - at < choose {
            return;
        }
        for index in at..=values.len() - choose {
            visit(
                values,
                choose - 1,
                index + 1,
                mask | (1 << values[index]),
                output,
            );
        }
    }
    let mut output = Vec::new();
    visit(values, choose, 0, 0, &mut output);
    output
}

fn render(n: usize, mask: u64) -> Vec<String> {
    (0..n)
        .map(|row| {
            (0..n)
                .map(|column| {
                    if mask & (1 << (row * n + column)) != 0 {
                        'U'
                    } else {
                        '.'
                    }
                })
                .collect()
        })
        .collect()
}

fn census(n: usize, fixed_u: u64, groups: &[(Vec<usize>, usize)], layer_counts: Value) -> Value {
    let choices: Vec<Vec<u64>> = groups
        .iter()
        .map(|(positions, choose)| combination_masks(positions, *choose))
        .collect();
    let edges = dual_edges(n);
    let vertices = 1 + (n - 1) * (n - 1);
    let mut rank_histogram = BTreeMap::<usize, u64>::new();
    let mut cycle_histogram = BTreeMap::<usize, u64>::new();
    let mut patterns = 0u64;
    let mut connected = 0u64;
    let mut maximum_rank = 0usize;
    let mut maximum_edges = 0usize;
    let mut maximum_rank_at_maximum_edges = 0usize;
    let mut minimum_cycles_at_maximum_edges = usize::MAX;
    let mut best_maximum_edge_mask = 0u64;
    let mut best_cycle = usize::MAX;
    let mut best_mask = 0u64;

    fn enumerate(
        depth: usize,
        mask: u64,
        choices: &[Vec<u64>],
        edges: &[DualEdge],
        vertices: usize,
        patterns: &mut u64,
        connected: &mut u64,
        maximum_rank: &mut usize,
        maximum_edges: &mut usize,
        maximum_rank_at_maximum_edges: &mut usize,
        minimum_cycles_at_maximum_edges: &mut usize,
        best_maximum_edge_mask: &mut u64,
        best_cycle: &mut usize,
        best_mask: &mut u64,
        rank_histogram: &mut BTreeMap<usize, u64>,
        cycle_histogram: &mut BTreeMap<usize, u64>,
    ) {
        if depth < choices.len() {
            for &addition in &choices[depth] {
                enumerate(
                    depth + 1,
                    mask | addition,
                    choices,
                    edges,
                    vertices,
                    patterns,
                    connected,
                    maximum_rank,
                    maximum_edges,
                    maximum_rank_at_maximum_edges,
                    minimum_cycles_at_maximum_edges,
                    best_maximum_edge_mask,
                    best_cycle,
                    best_mask,
                    rank_histogram,
                    cycle_histogram,
                );
            }
            return;
        }
        *patterns += 1;
        let mut dsu = Dsu::new(vertices);
        let mut rank = 0usize;
        let mut edge_count = 0usize;
        for edge in edges {
            if mask & edge.primal_mask == edge.primal_mask {
                edge_count += 1;
                rank += usize::from(dsu.union(edge.left, edge.right));
            }
        }
        let cycles = edge_count - rank;
        if edge_count > *maximum_edges {
            *maximum_edges = edge_count;
            *maximum_rank_at_maximum_edges = rank;
            *minimum_cycles_at_maximum_edges = cycles;
            *best_maximum_edge_mask = mask;
        } else if edge_count == *maximum_edges {
            *maximum_rank_at_maximum_edges = (*maximum_rank_at_maximum_edges).max(rank);
            if cycles < *minimum_cycles_at_maximum_edges {
                *minimum_cycles_at_maximum_edges = cycles;
                *best_maximum_edge_mask = mask;
            }
        }
        *rank_histogram.entry(rank).or_default() += 1;
        *cycle_histogram.entry(cycles).or_default() += 1;
        *connected += u64::from(rank + 1 == vertices);
        if rank > *maximum_rank || (rank == *maximum_rank && cycles < *best_cycle) {
            *maximum_rank = rank;
            *best_cycle = cycles;
            *best_mask = mask;
        }
    }

    enumerate(
        0,
        fixed_u,
        &choices,
        &edges,
        vertices,
        &mut patterns,
        &mut connected,
        &mut maximum_rank,
        &mut maximum_edges,
        &mut maximum_rank_at_maximum_edges,
        &mut minimum_cycles_at_maximum_edges,
        &mut best_maximum_edge_mask,
        &mut best_cycle,
        &mut best_mask,
        &mut rank_histogram,
        &mut cycle_histogram,
    );
    json!({
        "n": n,
        "patterns": patterns,
        "u_count": best_mask.count_ones(),
        "full_count": n * n - best_mask.count_ones() as usize,
        "layer_full_counts": layer_counts,
        "connected_patterns": connected,
        "required_rank": vertices - 1,
        "maximum_rank": maximum_rank,
        "maximum_dual_edges": maximum_edges,
        "maximum_rank_at_maximum_edges": maximum_rank_at_maximum_edges,
        "minimum_components_at_maximum_edges": vertices - maximum_rank_at_maximum_edges,
        "minimum_cycles_at_maximum_edges": minimum_cycles_at_maximum_edges,
        "maximum_edge_pattern": render(n, best_maximum_edge_mask),
        "minimum_run_sum": 2 * best_mask.count_ones() as usize - maximum_edges,
        "minimum_component_count": vertices - maximum_rank,
        "minimum_cycle_at_maximum_rank": best_cycle,
        "rank_histogram": rank_histogram,
        "cycle_histogram": cycle_histogram,
        "rank_maximizing_pattern": render(n, best_mask),
    })
}

fn n5() -> Value {
    let n = 5;
    let inner = boundary(n, 1);
    let outer = boundary(n, 0);
    let fixed = inner
        .into_iter()
        .fold(0u64, |mask, vertex| mask | (1 << vertex));
    census(
        n,
        fixed,
        &[(outer, 4)],
        json!({"side_5_boundary":12,"side_3_boundary":0,"center":1}),
    )
}

fn n8() -> Value {
    let n = 8;
    let side6 = boundary(n, 1);
    let side4 = boundary(n, 2);
    let side4_corners = corners(n, 2);
    let side4_noncorner: Vec<_> = side4
        .into_iter()
        .filter(|vertex| !side4_corners.contains(vertex))
        .collect();
    let side2 = boundary(n, 3);
    let outer_corners = corners(n, 0);
    let outer_noncorner: Vec<_> = boundary(n, 0)
        .into_iter()
        .filter(|vertex| !outer_corners.contains(vertex))
        .collect();
    let fixed = side6
        .into_iter()
        .chain(side4_corners)
        .fold(0u64, |mask, vertex| mask | (1 << vertex));
    census(
        n,
        fixed,
        &[(outer_noncorner, 4), (side4_noncorner, 4), (side2, 2)],
        json!({"side_8_boundary":24,"side_6_boundary":0,"side_4_boundary":4,"side_2_boundary":2}),
    )
}

fn main() {
    let mut output = None::<PathBuf>;
    let args: Vec<_> = env::args().skip(1).collect();
    let mut at = 0;
    while at < args.len() {
        match args[at].as_str() {
            "--output" => {
                output = Some(PathBuf::from(
                    args.get(at + 1).expect("missing --output path"),
                ));
                at += 2;
            }
            value => panic!("unknown argument {value}"),
        }
    }
    let report = json!({
        "schema":"grid-graphs.concentric-layer-rank-census.v1",
        "scope": {"semantics":"exact-enumeration-of-declared-layer-count-patterns"},
        "cases": {"n5-scalar-optimum":n5(),"n8-scalar-optimum":n8()},
    });
    let rendered = serde_json::to_string_pretty(&report).unwrap() + "\n";
    if let Some(path) = output {
        fs::write(path, rendered).unwrap();
    } else {
        print!("{rendered}");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn n5_census_has_rank_deficit_two() {
        let report = n5();
        assert_eq!(report["patterns"], 1820);
        assert_eq!(report["maximum_rank"], 14);
        assert_eq!(report["connected_patterns"], 0);
    }
}
