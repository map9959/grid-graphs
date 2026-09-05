//! Exact weighted row grammar for 3|F|+2g(F).
//!
//! This is the compact execution engine for the readable Python specification
//! in `analysis/gap_inequality_falsification.py`. A line gap is a pair of
//! consecutive maximal F-runs, both of length at least two.

use fxhash::FxHashMap;
use serde::Serialize;

#[derive(Clone, Copy, Hash, Eq, PartialEq)]
struct Key {
    mask: u16,
    partition: u64,
    vertical: u32,
}

#[derive(Clone, Copy)]
struct Value {
    score: i16,
    rows: u128,
}

#[derive(Serialize)]
struct ResultRow {
    n: usize,
    maximum: i16,
    bound: i16,
    margin: i16,
    forced_count: u32,
    gaps: u32,
    rows: Vec<u16>,
    layer_states: Vec<usize>,
}

struct Dsu {
    parent: [u8; 20],
}

impl Dsu {
    fn new() -> Self {
        let mut parent = [0; 20];
        for (index, item) in parent.iter_mut().enumerate() {
            *item = index as u8;
        }
        Self { parent }
    }

    fn root(&mut self, vertex: usize) -> usize {
        let parent = self.parent[vertex] as usize;
        if parent != vertex {
            let root = self.root(parent);
            self.parent[vertex] = root as u8;
        }
        self.parent[vertex] as usize
    }

    fn summary_union(&mut self, left: usize, right: usize) {
        let left = self.root(left);
        let right = self.root(right);
        if left != right {
            self.parent[right] = left as u8;
        }
    }

    fn edge_union(&mut self, left: usize, right: usize) -> bool {
        let left = self.root(left);
        let right = self.root(right);
        if left == right {
            return false;
        }
        self.parent[right] = left as u8;
        true
    }
}

fn canonical(dsu: &mut Dsu, start: usize, n: usize) -> u64 {
    let mut roots = [usize::MAX; 10];
    let mut labels = 0usize;
    let mut packed = 0u64;
    for column in 0..n {
        let root = dsu.root(start + column);
        let label = match roots[..labels].iter().position(|item| *item == root) {
            Some(label) => label,
            None => {
                roots[labels] = root;
                labels += 1;
                labels - 1
            }
        };
        packed |= (label as u64) << (4 * column);
    }
    packed
}

fn first_state(n: usize, mask: u16) -> Option<u64> {
    let mut dsu = Dsu::new();
    for column in 0..n - 1 {
        if mask & (3 << column) != 0 && !dsu.edge_union(column, column + 1) {
            return None;
        }
    }
    Some(canonical(&mut dsu, 0, n))
}

fn forest_transition(n: usize, key: Key, mask: u16) -> Option<u64> {
    let mut dsu = Dsu::new();
    let mut representative = [usize::MAX; 10];
    for column in 0..n {
        let label = ((key.partition >> (4 * column)) & 15) as usize;
        if representative[label] == usize::MAX {
            representative[label] = column;
        } else {
            dsu.summary_union(representative[label], column);
        }
    }
    for column in 0..n {
        if (key.mask | mask) & (1 << column) != 0 && !dsu.edge_union(column, n + column) {
            return None;
        }
    }
    for column in 0..n - 1 {
        if mask & (3 << column) != 0 && !dsu.edge_union(n + column, n + column + 1) {
            return None;
        }
    }
    Some(canonical(&mut dsu, n, n))
}

fn line_step(state: u32, forced: bool) -> (u32, u32) {
    if forced {
        match state {
            0 => (1, 0),
            1 => (2, 0),
            2 => (2, 0),
            3 => (4, 0),
            4 => (2, 1),
            _ => unreachable!(),
        }
    } else {
        match state {
            0 | 1 | 4 => (0, 0),
            2 | 3 => (3, 0),
            _ => unreachable!(),
        }
    }
}

fn line_gaps(n: usize, mask: u16) -> u32 {
    let mut state = 0;
    let mut gaps = 0;
    for column in 0..n {
        (state, gaps) = {
            let (next, gain) = line_step(state, mask & (1 << column) != 0);
            (next, gaps + gain)
        };
    }
    gaps
}

fn vertical_step(n: usize, mut packed: u32, mask: u16) -> (u32, u32) {
    let mut result = 0;
    let mut place = 1;
    let mut gaps = 0;
    for column in 0..n {
        let state = packed % 5;
        packed /= 5;
        let (next, gain) = line_step(state, mask & (1 << column) != 0);
        result += place * next;
        place *= 5;
        gaps += gain;
    }
    (result, gaps)
}

fn direct_score(n: usize, rows: &[u16]) -> (i16, u32, u32) {
    let forced = rows.iter().map(|mask| mask.count_ones()).sum::<u32>();
    let horizontal = rows.iter().map(|mask| line_gaps(n, *mask)).sum::<u32>();
    let mut vertical = 0;
    for column in 0..n {
        let mut state = 0;
        for mask in rows {
            let (next, gain) = line_step(state, mask & (1 << column) != 0);
            state = next;
            vertical += gain;
        }
    }
    let gaps = horizontal + vertical;
    ((3 * forced + 2 * gaps) as i16, forced, gaps)
}

fn minimum_suffix_differences(remaining: usize) -> [[i16; 5]; 5] {
    let mut differences = [[0i16; 5]; 5];
    for _ in 0..remaining {
        let old = differences;
        for left in 0..5 {
            for right in 0..5 {
                differences[left][right] = [false, true]
                    .into_iter()
                    .map(|bit| {
                        let (next_left, gain_left) = line_step(left as u32, bit);
                        let (next_right, gain_right) = line_step(right as u32, bit);
                        gain_left as i16 - gain_right as i16
                            + old[next_left as usize][next_right as usize]
                    })
                    .min()
                    .unwrap();
            }
        }
    }
    differences
}

fn dominates(
    n: usize,
    left_vertical: u32,
    left_score: i16,
    right_vertical: u32,
    right_score: i16,
    differences: &[[i16; 5]; 5],
) -> bool {
    let mut left = left_vertical;
    let mut right = right_vertical;
    let mut worst_advantage = left_score - right_score;
    for _ in 0..n {
        worst_advantage += 2 * differences[(left % 5) as usize][(right % 5) as usize];
        left /= 5;
        right /= 5;
    }
    worst_advantage >= 0
}

fn prune_dominated(
    n: usize,
    remaining: usize,
    costs: FxHashMap<Key, Value>,
) -> FxHashMap<Key, Value> {
    let differences = minimum_suffix_differences(remaining);
    let mut groups: FxHashMap<(u16, u64), Vec<(u32, Value)>> = FxHashMap::default();
    for (key, value) in costs {
        let group = groups.entry((key.mask, key.partition)).or_default();
        if group.iter().any(|(vertical, old)| {
            dominates(
                n,
                *vertical,
                old.score,
                key.vertical,
                value.score,
                &differences,
            )
        }) {
            continue;
        }
        group.retain(|(vertical, old)| {
            !dominates(
                n,
                key.vertical,
                value.score,
                *vertical,
                old.score,
                &differences,
            )
        });
        group.push((key.vertical, value));
    }
    groups
        .into_iter()
        .flat_map(|((mask, partition), entries)| {
            entries.into_iter().map(move |(vertical, value)| {
                (
                    Key {
                        mask,
                        partition,
                        vertical,
                    },
                    value,
                )
            })
        })
        .collect()
}

fn solve(n: usize) -> ResultRow {
    assert!(
        (1..=10).contains(&n),
        "packed witness engine supports n <= 10"
    );
    let limit = 1u16 << n;
    let horizontal: Vec<u32> = (0..limit).map(|mask| line_gaps(n, mask)).collect();
    let mut costs = FxHashMap::default();
    for mask in 0..limit {
        if let Some(partition) = first_state(n, mask) {
            let (vertical, gain) = vertical_step(n, 0, mask);
            costs.insert(
                Key {
                    mask,
                    partition,
                    vertical,
                },
                Value {
                    score: (3 * mask.count_ones() + 2 * (horizontal[mask as usize] + gain)) as i16,
                    rows: mask as u128,
                },
            );
        }
    }
    let mut layer_states = vec![costs.len()];
    for row in 1..n {
        let mut next: FxHashMap<Key, Value> = FxHashMap::default();
        for (key, value) in costs.drain() {
            for mask in 0..limit {
                let Some(partition) = forest_transition(n, key, mask) else {
                    continue;
                };
                let (vertical, gain) = vertical_step(n, key.vertical, mask);
                let next_key = Key {
                    mask,
                    partition,
                    vertical,
                };
                let score = value.score
                    + (3 * mask.count_ones() + 2 * (horizontal[mask as usize] + gain)) as i16;
                let candidate = Value {
                    score,
                    rows: value.rows | ((mask as u128) << (n * row)),
                };
                match next.get_mut(&next_key) {
                    Some(old) if old.score < score => *old = candidate,
                    None => {
                        next.insert(next_key, candidate);
                    }
                    _ => {}
                }
            }
        }
        costs = prune_dominated(n, n - row - 1, next);
        layer_states.push(costs.len());
    }
    let best = costs.values().max_by_key(|value| value.score).unwrap();
    let row_mask = (1u128 << n) - 1;
    let rows: Vec<u16> = (0..n)
        .map(|row| ((best.rows >> (n * row)) & row_mask) as u16)
        .collect();
    let (replayed, forced_count, gaps) = direct_score(n, &rows);
    assert_eq!(replayed, best.score);
    let bound = (n * n + 3 * n - 4) as i16;
    ResultRow {
        n,
        maximum: best.score,
        bound,
        margin: bound - best.score,
        forced_count,
        gaps,
        rows,
        layer_states,
    }
}

fn main() {
    let through = std::env::args()
        .nth(1)
        .map(|value| value.parse::<usize>().expect("through must be an integer"))
        .unwrap_or(10);
    let results: Vec<_> = (2..=through).map(solve).collect();
    println!("{}", serde_json::to_string_pretty(&results).unwrap());
    if results.iter().any(|item| item.margin < 0) {
        std::process::exit(1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn line_automaton_examples() {
        assert_eq!(line_gaps(6, 0b110011), 1);
        assert_eq!(line_gaps(7, 0b1101011), 0);
    }

    #[test]
    fn known_small_exact_scores() {
        let expected = [(2, 6), (3, 12), (4, 24), (5, 34), (6, 49)];
        for (n, maximum) in expected {
            assert_eq!(solve(n).maximum, maximum);
        }
    }
}
