//! Fixed-target SAT search for a set U whose eligible primal edges connect the planar dual.

use std::collections::{HashSet, VecDeque};
use std::env;
use std::fmt::Write as _;
use std::fs;
use std::io::BufWriter;
use std::path::PathBuf;
use std::process;
use std::time::{Duration, Instant};
use varisat::{CnfFormula, ExtendFormula, Lit, Solver, Var};
use varisat_dimacs::write_dimacs;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum StaticCuts {
    Singleton,
    Interval,
    SmallRect,
    AllRect,
}

impl StaticCuts {
    fn parse(value: &str) -> Result<Self, String> {
        match value {
            "singleton" => Ok(Self::Singleton),
            "interval" => Ok(Self::Interval),
            "small-rect" => Ok(Self::SmallRect),
            "all-rect" => Ok(Self::AllRect),
            _ => Err(format!(
                "invalid --static-cuts value {value:?}; expected singleton|interval|small-rect|all-rect"
            )),
        }
    }

    fn name(self) -> &'static str {
        match self {
            Self::Singleton => "singleton",
            Self::Interval => "interval",
            Self::SmallRect => "small-rect",
            Self::AllRect => "all-rect",
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Symmetry {
    None,
    D4,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Connectivity {
    Rooted,
    Lazy,
}

impl Connectivity {
    fn parse(value: &str) -> Result<Self, String> {
        match value {
            "rooted" => Ok(Self::Rooted),
            "lazy" => Ok(Self::Lazy),
            _ => Err(format!(
                "invalid --connectivity value {value:?}; expected rooted|lazy"
            )),
        }
    }

    fn name(self) -> &'static str {
        match self {
            Self::Rooted => "rooted",
            Self::Lazy => "lazy",
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Cardinality {
    Binary,
    Sequential,
}

impl Cardinality {
    fn parse(value: &str) -> Result<Self, String> {
        match value {
            "binary" => Ok(Self::Binary),
            "sequential" => Ok(Self::Sequential),
            _ => Err(format!(
                "invalid --cardinality value {value:?}; expected binary|sequential"
            )),
        }
    }

    fn name(self) -> &'static str {
        match self {
            Self::Binary => "binary",
            Self::Sequential => "sequential",
        }
    }
}

impl Symmetry {
    fn parse(value: &str) -> Result<Self, String> {
        match value {
            "none" => Ok(Self::None),
            "d4" => Ok(Self::D4),
            _ => Err(format!(
                "invalid --symmetry value {value:?}; expected none|d4"
            )),
        }
    }

    fn name(self) -> &'static str {
        match self {
            Self::None => "none",
            Self::D4 => "d4",
        }
    }
}

#[derive(Debug)]
struct Config {
    n: usize,
    u_count: usize,
    edge_min: Option<usize>,
    edge_max: Option<usize>,
    static_cuts: StaticCuts,
    symmetry: Symmetry,
    connectivity: Connectivity,
    cardinality: Cardinality,
    time_limit: Option<Duration>,
    seed: Option<u64>,
    near_hint: Option<PathBuf>,
    hint_exchanges: Option<usize>,
    output: Option<PathBuf>,
    json: Option<PathBuf>,
    dimacs_out: Option<PathBuf>,
    model_in: Option<PathBuf>,
    max_rounds: usize,
}

impl Config {
    fn parse() -> Result<Self, String> {
        let mut n = None;
        let mut u_count = None;
        let mut edge_min = None;
        let mut edge_max = None;
        let mut static_cuts = StaticCuts::Singleton;
        let mut symmetry = Symmetry::None;
        let mut connectivity = Connectivity::Rooted;
        let mut cardinality = Cardinality::Binary;
        let mut time_limit = None;
        let seed = None;
        let mut near_hint = None;
        let mut hint_exchanges = None;
        let mut output = None;
        let mut json = None;
        let mut dimacs_out = None;
        let mut model_in = None;
        let mut max_rounds = 10_000usize;
        let args: Vec<String> = env::args().skip(1).collect();
        let mut i = 0;
        while i < args.len() {
            let flag = &args[i];
            if flag == "--help" || flag == "-h" {
                print_usage();
                process::exit(0);
            }
            i += 1;
            let value = args
                .get(i)
                .ok_or_else(|| format!("missing value for {flag}"))?;
            i += 1;
            match flag.as_str() {
                "--n" => n = Some(parse_usize(flag, value)?),
                "--u-count" => u_count = Some(parse_usize(flag, value)?),
                "--edge-min" => edge_min = Some(parse_usize(flag, value)?),
                "--edge-max" => edge_max = Some(parse_usize(flag, value)?),
                "--static-cuts" => static_cuts = StaticCuts::parse(value)?,
                "--symmetry" => symmetry = Symmetry::parse(value)?,
                "--connectivity" => connectivity = Connectivity::parse(value)?,
                "--cardinality" => cardinality = Cardinality::parse(value)?,
                "--time-limit-seconds" => {
                    let seconds = value
                        .parse::<f64>()
                        .map_err(|_| format!("invalid number for {flag}: {value:?}"))?;
                    if !seconds.is_finite() || seconds < 0.0 {
                        return Err(format!("{flag} must be a finite non-negative number"));
                    }
                    time_limit = Some(Duration::from_secs_f64(seconds));
                }
                "--seed" => {
                    value
                        .parse::<u64>()
                        .map_err(|_| format!("invalid integer for {flag}: {value:?}"))?;
                    return Err("--seed is unsupported because Varisat 0.2 has no seed API".into());
                }
                "--near-hint" => near_hint = Some(PathBuf::from(value)),
                "--hint-exchanges" => hint_exchanges = Some(parse_usize(flag, value)?),
                "--output" => output = Some(PathBuf::from(value)),
                "--json" => json = Some(PathBuf::from(value)),
                "--dimacs-out" => dimacs_out = Some(PathBuf::from(value)),
                "--model-in" => model_in = Some(PathBuf::from(value)),
                "--max-rounds" => max_rounds = parse_usize(flag, value)?,
                _ => return Err(format!("unknown option {flag:?}")),
            }
        }
        let config = Self {
            n: n.ok_or("--n is required")?,
            u_count: u_count.ok_or("--u-count is required")?,
            edge_min,
            edge_max,
            static_cuts,
            symmetry,
            connectivity,
            cardinality,
            time_limit,
            seed,
            near_hint,
            hint_exchanges,
            output,
            json,
            dimacs_out,
            model_in,
            max_rounds,
        };
        config.validate()?;
        Ok(config)
    }

    fn validate(&self) -> Result<(), String> {
        if self.n == 0 {
            return Err("--n must be at least 1".into());
        }
        let vertices = self.n.checked_mul(self.n).ok_or("--n is too large")?;
        let edges = self
            .n
            .checked_mul(self.n - 1)
            .and_then(|v| v.checked_mul(2))
            .ok_or("--n is too large")?;
        if self.u_count > vertices {
            return Err(format!("--u-count cannot exceed {vertices}"));
        }
        if self.edge_min.is_some_and(|v| v > edges) || self.edge_max.is_some_and(|v| v > edges) {
            return Err(format!("edge bounds cannot exceed {edges}"));
        }
        if let (Some(min), Some(max)) = (self.edge_min, self.edge_max) {
            if min > max {
                return Err("--edge-min cannot exceed --edge-max".into());
            }
        }
        if self.max_rounds == 0 {
            return Err("--max-rounds must be at least 1".into());
        }
        if self.hint_exchanges.is_some() && self.near_hint.is_none() {
            return Err("--hint-exchanges requires --near-hint".into());
        }
        if self.dimacs_out.is_some() && self.model_in.is_some() {
            return Err("--dimacs-out and --model-in are mutually exclusive".into());
        }
        if self.dimacs_out.is_some() && (self.output.is_some() || self.json.is_some()) {
            return Err("--dimacs-out cannot be combined with --output or --json".into());
        }
        if self.dimacs_out.is_some() && self.connectivity == Connectivity::Lazy {
            return Err(
                "--dimacs-out requires --connectivity rooted; lazy cuts are incremental".into(),
            );
        }
        Ok(())
    }
}

fn parse_usize(flag: &str, value: &str) -> Result<usize, String> {
    value
        .parse()
        .map_err(|_| format!("invalid integer for {flag}: {value:?}"))
}

fn print_usage() {
    eprintln!(
        "Usage: search_n17_sat --n N --u-count K [options]\n\
         Options:\n\
           --edge-min K --edge-max K\n\
           --static-cuts singleton|interval|small-rect|all-rect\n\
           --symmetry none|d4\n\
           --connectivity rooted|lazy\n\
           --cardinality binary|sequential\n\
           --time-limit-seconds S       (soft; checked only between Varisat solve rounds)\n\
           --max-rounds R\n\
           --seed S                     (unsupported by Varisat 0.2)\n\
           --near-hint PATH             (seed globally valid cuts from a pattern/witness)\n\
           --hint-exchanges K           (search within K same-cardinality exchanges)\n\
           --dimacs-out PATH            (export the complete static CNF and exit)\n\
           --model-in PATH              (validate a competition-format SAT model)\n\
           --output PATH --json PATH"
    );
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct PrimalEdge {
    a: usize,
    b: usize,
    dual_a: usize,
    dual_b: usize,
}

#[derive(Debug)]
struct Grid {
    n: usize,
    edges: Vec<PrimalEdge>,
    face_count: usize,
    out: usize,
}

impl Grid {
    fn new(n: usize) -> Self {
        let side = n.saturating_sub(1);
        let face_count = side * side;
        let out = face_count;
        let face = |r: usize, c: usize| r * side + c;
        let mut edges = Vec::with_capacity(2 * n * side);

        for r in 0..n {
            for c in 0..side {
                let dual_a = if r == 0 { out } else { face(r - 1, c) };
                let dual_b = if r == side { out } else { face(r, c) };
                edges.push(PrimalEdge {
                    a: r * n + c,
                    b: r * n + c + 1,
                    dual_a,
                    dual_b,
                });
            }
        }
        for r in 0..side {
            for c in 0..n {
                let dual_a = if c == 0 { out } else { face(r, c - 1) };
                let dual_b = if c == side { out } else { face(r, c) };
                edges.push(PrimalEdge {
                    a: r * n + c,
                    b: (r + 1) * n + c,
                    dual_a,
                    dual_b,
                });
            }
        }
        Self {
            n,
            edges,
            face_count,
            out,
        }
    }

    fn dual_node_count(&self) -> usize {
        self.face_count + 1
    }
}

fn encode_and(formula: &mut CnfFormula, y: Var, a: Var, b: Var) {
    formula.add_clause(&[!y.positive(), a.positive()]);
    formula.add_clause(&[!y.positive(), b.positive()]);
    formula.add_clause(&[!a.positive(), !b.positive(), y.positive()]);
}

fn encode_xor(formula: &mut CnfFormula, output: Var, a: Lit, b: Lit) {
    let output = output.positive();
    formula.add_clause(&[!a, !b, !output]);
    formula.add_clause(&[a, b, !output]);
    formula.add_clause(&[a, !b, output]);
    formula.add_clause(&[!a, b, output]);
}

fn encode_lit_and(formula: &mut CnfFormula, output: Var, a: Lit, b: Lit) {
    let output = output.positive();
    formula.add_clause(&[!output, a]);
    formula.add_clause(&[!output, b]);
    formula.add_clause(&[output, !a, !b]);
}

/// Return an exact little-endian binary sum. Ripple addition uses O(n log n)
/// variables, avoiding the quadratic blow-up of two unary exact counters.
fn encode_binary_sum(formula: &mut CnfFormula, literals: &[Lit]) -> Vec<Lit> {
    debug_assert!(!literals.is_empty());
    let width = (usize::BITS - literals.len().leading_zeros()) as usize;
    let zero_vars: Vec<Var> = formula.new_var_iter(width).collect();
    let mut sum = Vec::with_capacity(width);
    for var in zero_vars {
        formula.add_clause(&[!var.positive()]);
        sum.push(var.positive());
    }
    for &literal in literals {
        let mut carry = literal;
        let mut next = Vec::with_capacity(width);
        for &bit in &sum {
            let output = formula.new_var();
            encode_xor(formula, output, bit, carry);
            next.push(output.positive());
            let next_carry = formula.new_var();
            encode_lit_and(formula, next_carry, bit, carry);
            carry = next_carry.positive();
        }
        formula.add_clause(&[!carry]);
        sum = next;
    }
    sum
}

fn forbid_sum_value(formula: &mut CnfFormula, sum: &[Lit], value: usize) {
    let clause: Vec<Lit> = sum
        .iter()
        .enumerate()
        .map(|(bit, &literal)| {
            if value & (1 << bit) == 0 {
                literal
            } else {
                !literal
            }
        })
        .collect();
    formula.add_clause(&clause);
}

fn encode_at_most_small(formula: &mut CnfFormula, literals: &[Lit], k: usize) {
    if k >= literals.len() {
        return;
    }
    if k == 0 {
        for &literal in literals {
            formula.add_clause(&[!literal]);
        }
        return;
    }
    let counters: Vec<Vec<Var>> = (0..literals.len() - 1)
        .map(|_| formula.new_var_iter(k).collect())
        .collect();
    formula.add_clause(&[!literals[0], counters[0][0].positive()]);
    for i in 1..literals.len() - 1 {
        formula.add_clause(&[!literals[i], counters[i][0].positive()]);
        formula.add_clause(&[!counters[i - 1][0].positive(), counters[i][0].positive()]);
        for j in 1..k {
            formula.add_clause(&[
                !literals[i],
                !counters[i - 1][j - 1].positive(),
                counters[i][j].positive(),
            ]);
            formula.add_clause(&[!counters[i - 1][j].positive(), counters[i][j].positive()]);
        }
        formula.add_clause(&[!literals[i], !counters[i - 1][k - 1].positive()]);
    }
    formula.add_clause(&[
        !literals[literals.len() - 1],
        !counters[literals.len() - 2][k - 1].positive(),
    ]);
}

fn encode_at_most(formula: &mut CnfFormula, literals: &[Lit], k: usize) {
    if k >= literals.len() {
        return;
    }
    if k <= 16 {
        encode_at_most_small(formula, literals, k);
        return;
    }
    let sum = encode_binary_sum(formula, literals);
    for value in k + 1..=literals.len() {
        forbid_sum_value(formula, &sum, value);
    }
}

fn encode_at_least(formula: &mut CnfFormula, literals: &[Lit], k: usize) {
    if k == 0 {
        return;
    }
    if k > literals.len() {
        formula.add_clause(&[]);
        return;
    }
    if literals.len() - k <= 16 {
        let negated: Vec<Lit> = literals.iter().map(|&literal| !literal).collect();
        encode_at_most_small(formula, &negated, literals.len() - k);
        return;
    }
    if k == 1 {
        formula.add_clause(literals);
        return;
    }
    let sum = encode_binary_sum(formula, literals);
    for value in 0..k {
        forbid_sum_value(formula, &sum, value);
    }
}

fn encode_exactly(formula: &mut CnfFormula, literals: &[Lit], k: usize) {
    if k > literals.len() {
        formula.add_clause(&[]);
        return;
    }
    if literals.is_empty() {
        return;
    }
    let sum = encode_binary_sum(formula, literals);
    for (bit, &literal) in sum.iter().enumerate() {
        formula.add_clause(&[if k & (1 << bit) != 0 {
            literal
        } else {
            !literal
        }]);
    }
}

fn encode_at_most_with(formula: &mut CnfFormula, literals: &[Lit], k: usize, mode: Cardinality) {
    match mode {
        Cardinality::Binary => encode_at_most(formula, literals, k),
        Cardinality::Sequential => encode_at_most_small(formula, literals, k),
    }
}

fn encode_at_least_with(formula: &mut CnfFormula, literals: &[Lit], k: usize, mode: Cardinality) {
    match mode {
        Cardinality::Binary => encode_at_least(formula, literals, k),
        Cardinality::Sequential => {
            if k > literals.len() {
                formula.add_clause(&[]);
            } else {
                let negated: Vec<Lit> = literals.iter().map(|&literal| !literal).collect();
                encode_at_most_small(formula, &negated, literals.len() - k);
            }
        }
    }
}

fn encode_exactly_with(formula: &mut CnfFormula, literals: &[Lit], k: usize, mode: Cardinality) {
    match mode {
        Cardinality::Binary => encode_exactly(formula, literals, k),
        Cardinality::Sequential => {
            if k > literals.len() {
                formula.add_clause(&[]);
            } else {
                encode_at_most_small(formula, literals, k);
                let negated: Vec<Lit> = literals.iter().map(|&literal| !literal).collect();
                encode_at_most_small(formula, &negated, literals.len() - k);
            }
        }
    }
}

fn d4_source_index(n: usize, transform: usize, index: usize) -> usize {
    let r = index / n;
    let c = index % n;
    let (source_r, source_c) = match transform {
        0 => (r, c),
        1 => (n - 1 - c, r),
        2 => (n - 1 - r, n - 1 - c),
        3 => (c, n - 1 - r),
        4 => (r, n - 1 - c),
        5 => (n - 1 - r, c),
        6 => (c, r),
        7 => (n - 1 - c, n - 1 - r),
        _ => panic!("D4 transform index must be in 0..8"),
    };
    source_r * n + source_c
}

fn encode_lex_leader(formula: &mut CnfFormula, left: &[Var], right: &[Var]) {
    let pairs: Vec<(Lit, Lit)> = left
        .iter()
        .zip(right)
        .filter_map(|(&a, &b)| (a != b).then_some((a.positive(), b.positive())))
        .collect();
    let Some(&(first_a, first_b)) = pairs.first() else {
        return;
    };
    formula.add_clause(&[!first_a, first_b]);
    if pairs.len() == 1 {
        return;
    }

    let prefix_equal: Vec<Var> = formula.new_var_iter(pairs.len() - 1).collect();
    formula.add_clause(&[!first_a, !first_b, prefix_equal[0].positive()]);
    formula.add_clause(&[first_a, first_b, prefix_equal[0].positive()]);
    for index in 1..pairs.len() {
        let (a, b) = pairs[index];
        let prefix = prefix_equal[index - 1].positive();
        formula.add_clause(&[!prefix, !a, b]);
        if index + 1 < pairs.len() {
            let next = prefix_equal[index].positive();
            formula.add_clause(&[!prefix, !a, !b, next]);
            formula.add_clause(&[!prefix, a, b, next]);
        }
    }
}

fn encode_d4_symmetry(formula: &mut CnfFormula, x: &[Var], n: usize) {
    for transform in 1..8 {
        let transformed: Vec<Var> = (0..x.len())
            .map(|index| x[d4_source_index(n, transform, index)])
            .collect();
        encode_lex_leader(formula, x, &transformed);
    }
}

fn is_d4_canonical(u: &[bool], n: usize) -> bool {
    (1..8).all(|transform| {
        (0..u.len())
            .map(|index| u[index].cmp(&u[d4_source_index(n, transform, index)]))
            .find(|ordering| !ordering.is_eq())
            .is_none_or(|ordering| ordering.is_lt())
    })
}

fn encode_guarded_xor(formula: &mut CnfFormula, guard: Lit, output: Lit, a: Lit, b: Lit) {
    formula.add_clause(&[!guard, !a, !b, !output]);
    formula.add_clause(&[!guard, a, b, !output]);
    formula.add_clause(&[!guard, a, !b, output]);
    formula.add_clause(&[!guard, !a, b, output]);
}

/// Select one parent edge for every bounded face and assign exact depths from
/// OUT. Parent depth + 1 = child depth rules out cycles and certifies that all
/// dual nodes reach OUT.
fn encode_rooted_connectivity(formula: &mut CnfFormula, grid: &Grid, y: &[Var]) -> Vec<Vec<Var>> {
    let node_count = grid.dual_node_count();
    let width = (usize::BITS - (node_count - 1).leading_zeros()) as usize;
    let depths: Vec<Vec<Var>> = (0..node_count)
        .map(|_| formula.new_var_iter(width).collect())
        .collect();
    for &bit in &depths[grid.out] {
        formula.add_clause(&[!bit.positive()]);
    }

    let mut incident_parents = vec![Vec::new(); node_count];
    let mut parents_by_edge = vec![Vec::new(); grid.edges.len()];
    for (edge_id, edge) in grid.edges.iter().enumerate() {
        for (child, parent) in [(edge.dual_a, edge.dual_b), (edge.dual_b, edge.dual_a)] {
            if child == grid.out {
                continue;
            }
            let arc = formula.new_var();
            let arc_lit = arc.positive();
            incident_parents[child].push(arc);
            parents_by_edge[edge_id].push(arc);
            formula.add_clause(&[!arc_lit, y[edge_id].positive()]);

            let child_bit = depths[child][0].positive();
            let parent_bit = depths[parent][0].positive();
            formula.add_clause(&[!arc_lit, child_bit, parent_bit]);
            formula.add_clause(&[!arc_lit, !child_bit, !parent_bit]);
            let mut carry = parent_bit;
            for bit in 1..width {
                encode_guarded_xor(
                    formula,
                    arc_lit,
                    depths[child][bit].positive(),
                    depths[parent][bit].positive(),
                    carry,
                );
                let next_carry = formula.new_var();
                encode_lit_and(formula, next_carry, depths[parent][bit].positive(), carry);
                carry = next_carry.positive();
            }
            formula.add_clause(&[!arc_lit, !carry]);
        }
    }

    for (node, parents) in incident_parents.iter().enumerate() {
        if node == grid.out {
            continue;
        }
        formula.add_clause(
            &parents
                .iter()
                .map(|parent| parent.positive())
                .collect::<Vec<_>>(),
        );
        for i in 0..parents.len() {
            for j in i + 1..parents.len() {
                formula.add_clause(&[!parents[i].positive(), !parents[j].positive()]);
            }
        }
    }
    parents_by_edge
}

fn encode_extra_edges(
    formula: &mut CnfFormula,
    y: &[Var],
    parents_by_edge: &[Vec<Var>],
) -> Vec<Lit> {
    y.iter()
        .zip(parents_by_edge)
        .map(|(&edge, parents)| {
            let extra = formula.new_var();
            formula.add_clause(&[!extra.positive(), edge.positive()]);
            for &parent in parents {
                formula.add_clause(&[!extra.positive(), !parent.positive()]);
            }
            let mut reverse = vec![!edge.positive(), extra.positive()];
            reverse.extend(parents.iter().map(|parent| parent.positive()));
            formula.add_clause(&reverse);
            extra.positive()
        })
        .collect()
}

fn rectangle_specs(grid: &Grid, mode: StaticCuts) -> Vec<(usize, usize, usize, usize)> {
    let side = grid.n.saturating_sub(1);
    let mut specs = Vec::new();
    for r0 in 0..side {
        for r1 in r0 + 1..=side {
            for c0 in 0..side {
                for c1 in c0 + 1..=side {
                    let h = r1 - r0;
                    let w = c1 - c0;
                    let include = match mode {
                        StaticCuts::Singleton => h == 1 && w == 1,
                        StaticCuts::Interval => h == 1 || w == 1,
                        StaticCuts::SmallRect => h <= 4 && w <= 4,
                        StaticCuts::AllRect => true,
                    };
                    if include {
                        specs.push((r0, r1, c0, c1));
                    }
                }
            }
        }
    }
    specs
}

fn rectangle_cut(grid: &Grid, spec: (usize, usize, usize, usize)) -> Vec<usize> {
    let (r0, r1, c0, c1) = spec;
    let side = grid.n - 1;
    let inside = |node: usize| {
        if node == grid.out {
            false
        } else {
            let r = node / side;
            let c = node % side;
            r0 <= r && r < r1 && c0 <= c && c < c1
        }
    };
    grid.edges
        .iter()
        .enumerate()
        .filter_map(|(id, edge)| (inside(edge.dual_a) != inside(edge.dual_b)).then_some(id))
        .collect()
}

#[derive(Default, Debug, Clone)]
struct Stats {
    base_variables: usize,
    total_variables: usize,
    base_clauses: usize,
    static_cut_candidates: usize,
    static_cut_clauses: usize,
    seeded_cut_candidates: usize,
    seeded_cut_clauses: usize,
    seeded_cut_duplicates: usize,
    near_hint_cardinality_matches_target: bool,
    solve_rounds: usize,
    disconnected_models: usize,
    lazy_component_candidates: usize,
    lazy_cut_clauses: usize,
    duplicate_cuts: usize,
}

#[derive(Debug)]
struct SatModel {
    u: Vec<bool>,
    y: Vec<bool>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Status {
    Witness,
    Unsat,
    TimeLimit,
    MaxRounds,
    SolverError,
}

impl Status {
    fn name(self) -> &'static str {
        match self {
            Self::Witness => "witness",
            Self::Unsat => "unsat",
            Self::TimeLimit => "incomplete",
            Self::MaxRounds => "max_rounds",
            Self::SolverError => "solver_error",
        }
    }

    fn exit_code(self) -> i32 {
        match self {
            Self::Witness | Self::Unsat => 0,
            Self::TimeLimit | Self::MaxRounds => 3,
            Self::SolverError => 4,
        }
    }
}

#[derive(Debug)]
struct SearchResult {
    status: Status,
    model: Option<SatModel>,
    stats: Stats,
    elapsed: Duration,
    message: Option<String>,
}

fn model_values(solver: &Solver<'_>) -> Vec<bool> {
    let model = solver.model().expect("SAT result has a model");
    let size = model.iter().map(|lit| lit.index() + 1).max().unwrap_or(0);
    let mut values = vec![false; size];
    for lit in model {
        values[lit.index()] = lit.is_positive();
    }
    values
}

fn dual_components(grid: &Grid, y: &[bool]) -> (Vec<usize>, usize) {
    let mut adjacency = vec![Vec::new(); grid.dual_node_count()];
    for (id, edge) in grid.edges.iter().enumerate() {
        if y[id] {
            adjacency[edge.dual_a].push(edge.dual_b);
            adjacency[edge.dual_b].push(edge.dual_a);
        }
    }
    let mut component = vec![usize::MAX; adjacency.len()];
    let mut count = 0;
    for start in 0..adjacency.len() {
        if component[start] != usize::MAX {
            continue;
        }
        component[start] = count;
        let mut queue = VecDeque::from([start]);
        while let Some(node) = queue.pop_front() {
            for &next in &adjacency[node] {
                if component[next] == usize::MAX {
                    component[next] = count;
                    queue.push_back(next);
                }
            }
        }
        count += 1;
    }
    (component, count)
}

fn component_cut(grid: &Grid, components: &[usize], target: usize) -> Vec<usize> {
    grid.edges
        .iter()
        .enumerate()
        .filter_map(|(id, edge)| {
            ((components[edge.dual_a] == target) != (components[edge.dual_b] == target))
                .then_some(id)
        })
        .collect()
}

fn component_union_cut(grid: &Grid, components: &[usize], selected: &[bool]) -> Vec<usize> {
    grid.edges
        .iter()
        .enumerate()
        .filter_map(|(id, edge)| {
            (selected[components[edge.dual_a]] != selected[components[edge.dual_b]]).then_some(id)
        })
        .collect()
}

fn separation_cuts(grid: &Grid, components: &[usize], component_count: usize) -> Vec<Vec<usize>> {
    let mut cuts: Vec<Vec<usize>> = (0..component_count)
        .map(|component| canonical_cut(component_cut(grid, components, component)))
        .collect();
    let mut sizes = vec![0usize; component_count];
    for &component in components {
        sizes[component] += 1;
    }
    let mut ordered: Vec<usize> = (0..component_count).collect();
    ordered.sort_unstable_by_key(|&component| (sizes[component], component));
    let mut selected = vec![false; component_count];
    for &component in ordered.iter().take(component_count.saturating_sub(1)) {
        selected[component] = true;
        cuts.push(canonical_cut(component_union_cut(
            grid, components, &selected,
        )));
    }
    cuts
}

fn canonical_cut(mut cut: Vec<usize>) -> Vec<usize> {
    cut.sort_unstable();
    cut.dedup();
    cut
}

fn parse_near_hint(contents: &str, n: usize) -> Result<Vec<bool>, String> {
    let mut rows = Vec::new();
    for (line_index, line) in contents.lines().enumerate() {
        let line = line.trim();
        if line.is_empty()
            || line.starts_with('#')
            || line.starts_with("U ")
            || line.starts_with("E ")
        {
            continue;
        }
        if !line.bytes().all(|ch| ch == b'.' || ch == b'U') {
            return Err(format!(
                "invalid near-hint content on line {}: expected only '.'/'U' pattern rows",
                line_index + 1
            ));
        }
        if line.len() != n {
            return Err(format!(
                "near-hint row on line {} has width {}, expected {n}",
                line_index + 1,
                line.len()
            ));
        }
        rows.push(line);
    }
    if rows.len() != n {
        return Err(format!(
            "near-hint has {} pattern rows, expected {n}",
            rows.len()
        ));
    }
    Ok(rows
        .into_iter()
        .flat_map(|row| row.bytes().map(|ch| ch == b'U'))
        .collect())
}

fn parse_competition_model(contents: &str, variables: &[Var]) -> Result<Vec<bool>, String> {
    let max_required = variables
        .iter()
        .map(|var| var.to_dimacs() as usize)
        .max()
        .unwrap_or(0);
    let mut assignments = vec![None; max_required + 1];
    let mut satisfiable = None;
    for (line_index, line) in contents.lines().enumerate() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('c') {
            continue;
        }
        if let Some(status) = line.strip_prefix('s') {
            let status = match status.trim() {
                "SATISFIABLE" => true,
                "UNSATISFIABLE" => false,
                other => return Err(format!("unsupported model status {other:?}")),
            };
            if satisfiable
                .replace(status)
                .is_some_and(|prior| prior != status)
            {
                return Err("conflicting model status lines".into());
            }
            continue;
        }
        let Some(values) = line.strip_prefix('v') else {
            return Err(format!(
                "unexpected model content on line {}: {line:?}",
                line_index + 1
            ));
        };
        for token in values.split_whitespace() {
            let literal = token.parse::<isize>().map_err(|_| {
                format!("invalid model literal {token:?} on line {}", line_index + 1)
            })?;
            if literal == 0 {
                continue;
            }
            let id = literal.unsigned_abs();
            if id > max_required {
                continue;
            }
            let value = literal > 0;
            if assignments[id]
                .replace(value)
                .is_some_and(|prior| prior != value)
            {
                return Err(format!("conflicting assignments for DIMACS variable {id}"));
            }
        }
    }
    if satisfiable != Some(true) {
        return Err("model file does not report SATISFIABLE".into());
    }
    variables
        .iter()
        .map(|var| {
            let id = var.to_dimacs() as usize;
            assignments[id].ok_or_else(|| format!("model omits required DIMACS variable {id}"))
        })
        .collect()
}

fn induced_y(grid: &Grid, u: &[bool]) -> Vec<bool> {
    grid.edges
        .iter()
        .map(|edge| u[edge.a] && u[edge.b])
        .collect()
}

fn near_hint_cuts(grid: &Grid, u: &[bool]) -> Vec<Vec<usize>> {
    let (components, component_count) = dual_components(grid, &induced_y(grid, u));
    let out_component = components[grid.out];
    (0..component_count)
        .filter(|&component| component != out_component)
        .map(|component| canonical_cut(component_cut(grid, &components, component)))
        .collect()
}

struct BuiltProblem {
    grid: Grid,
    formula: CnfFormula,
    x: Vec<Var>,
    y: Vec<Var>,
    seen_cuts: HashSet<Vec<usize>>,
    stats: Stats,
}

fn build_problem(config: &Config, near_hint: Option<&[bool]>) -> BuiltProblem {
    let grid = Grid::new(config.n);
    let mut formula = CnfFormula::new();
    let x: Vec<Var> = formula.new_var_iter(config.n * config.n).collect();
    let y: Vec<Var> = formula.new_var_iter(grid.edges.len()).collect();
    for (edge, &y_var) in grid.edges.iter().zip(&y) {
        encode_and(&mut formula, y_var, x[edge.a], x[edge.b]);
    }
    let x_lits: Vec<Lit> = x.iter().map(|v| v.positive()).collect();
    encode_exactly_with(&mut formula, &x_lits, config.u_count, config.cardinality);
    if config.symmetry == Symmetry::D4 {
        encode_d4_symmetry(&mut formula, &x, config.n);
    }
    if let (Some(hint), Some(exchanges)) = (near_hint, config.hint_exchanges) {
        let removals: Vec<Lit> = hint
            .iter()
            .zip(&x)
            .filter_map(|(&hint_u, var)| hint_u.then_some(!var.positive()))
            .collect();
        encode_at_most(&mut formula, &removals, exchanges);
    }
    let tree_edges = grid.dual_node_count() - 1;
    match config.connectivity {
        Connectivity::Rooted => {
            let parents_by_edge = encode_rooted_connectivity(&mut formula, &grid, &y);
            if config.edge_min.is_some() || config.edge_max.is_some() {
                let extra_edges = encode_extra_edges(&mut formula, &y, &parents_by_edge);
                if let Some(min) = config.edge_min {
                    encode_at_least_with(
                        &mut formula,
                        &extra_edges,
                        min.saturating_sub(tree_edges),
                        config.cardinality,
                    );
                }
                if let Some(max) = config.edge_max {
                    if max < tree_edges {
                        formula.add_clause(&[]);
                    } else {
                        encode_at_most_with(
                            &mut formula,
                            &extra_edges,
                            max - tree_edges,
                            config.cardinality,
                        );
                    }
                }
            }
        }
        Connectivity::Lazy => {
            let y_lits: Vec<Lit> = y.iter().map(|var| var.positive()).collect();
            if let Some(min) = config.edge_min {
                encode_at_least_with(&mut formula, &y_lits, min, config.cardinality);
            }
            if let Some(max) = config.edge_max {
                encode_at_most_with(&mut formula, &y_lits, max, config.cardinality);
            }
        }
    }

    let mut seen_cuts = HashSet::new();
    let mut stats = Stats {
        base_variables: x.len() + y.len(),
        near_hint_cardinality_matches_target: near_hint
            .is_some_and(|hint| hint.iter().filter(|&&is_u| is_u).count() == config.u_count),
        ..Stats::default()
    };
    for spec in rectangle_specs(&grid, config.static_cuts) {
        stats.static_cut_candidates += 1;
        let cut = canonical_cut(rectangle_cut(&grid, spec));
        if seen_cuts.insert(cut.clone()) {
            let clause: Vec<Lit> = cut.iter().map(|&id| y[id].positive()).collect();
            formula.add_clause(&clause);
            stats.static_cut_clauses += 1;
        } else {
            stats.duplicate_cuts += 1;
        }
    }
    if let Some(hint) = near_hint {
        for cut in near_hint_cuts(&grid, hint) {
            stats.seeded_cut_candidates += 1;
            if seen_cuts.insert(cut.clone()) {
                let clause: Vec<Lit> = cut.iter().map(|&id| y[id].positive()).collect();
                formula.add_clause(&clause);
                stats.seeded_cut_clauses += 1;
            } else {
                stats.seeded_cut_duplicates += 1;
                stats.duplicate_cuts += 1;
            }
        }
    }
    stats.total_variables = formula.var_count();
    stats.base_clauses = formula.len() - stats.static_cut_clauses - stats.seeded_cut_clauses;

    BuiltProblem {
        grid,
        formula,
        x,
        y,
        seen_cuts,
        stats,
    }
}

fn search(config: &Config, near_hint: Option<&[bool]>) -> SearchResult {
    let start = Instant::now();
    let BuiltProblem {
        grid,
        formula,
        x,
        y,
        mut seen_cuts,
        mut stats,
    } = build_problem(config, near_hint);

    let mut solver = Solver::new();
    solver.add_formula(&formula);
    loop {
        if config
            .time_limit
            .is_some_and(|limit| start.elapsed() >= limit)
        {
            return SearchResult {
                status: Status::TimeLimit,
                model: None,
                stats,
                elapsed: start.elapsed(),
                message: Some(
                    "soft time limit reached between solve rounds; search is incomplete".into(),
                ),
            };
        }
        if stats.solve_rounds >= config.max_rounds {
            return SearchResult {
                status: Status::MaxRounds,
                model: None,
                stats,
                elapsed: start.elapsed(),
                message: Some("maximum solve rounds reached".into()),
            };
        }
        stats.solve_rounds += 1;
        let satisfiable = match solver.solve() {
            Ok(value) => value,
            Err(error) => {
                return SearchResult {
                    status: Status::SolverError,
                    model: None,
                    stats,
                    elapsed: start.elapsed(),
                    message: Some(error.to_string()),
                }
            }
        };
        if !satisfiable {
            return SearchResult {
                status: Status::Unsat,
                model: None,
                stats,
                elapsed: start.elapsed(),
                message: None,
            };
        }

        let values = model_values(&solver);
        let model = SatModel {
            u: x.iter().map(|v| values[v.index()]).collect(),
            y: y.iter().map(|v| values[v.index()]).collect(),
        };
        let (components, component_count) = dual_components(&grid, &model.y);
        if component_count == 1 {
            if let Err(message) = verify_model(config, &grid, &model) {
                return SearchResult {
                    status: Status::SolverError,
                    model: None,
                    stats,
                    elapsed: start.elapsed(),
                    message: Some(format!("internal model verification failed: {message}")),
                };
            }
            return SearchResult {
                status: Status::Witness,
                model: Some(model),
                stats,
                elapsed: start.elapsed(),
                message: None,
            };
        }

        stats.disconnected_models += 1;
        for cut in separation_cuts(&grid, &components, component_count) {
            stats.lazy_component_candidates += 1;
            if seen_cuts.insert(cut.clone()) {
                let clause: Vec<Lit> = cut.iter().map(|&id| y[id].positive()).collect();
                solver.add_clause(&clause);
                stats.lazy_cut_clauses += 1;
            } else {
                stats.duplicate_cuts += 1;
            }
        }
    }
}

#[derive(Debug)]
struct Dsu {
    parent: Vec<usize>,
    rank: Vec<u8>,
}

impl Dsu {
    fn new(n: usize) -> Self {
        Self {
            parent: (0..n).collect(),
            rank: vec![0; n],
        }
    }

    fn find(&mut self, x: usize) -> usize {
        if self.parent[x] != x {
            self.parent[x] = self.find(self.parent[x]);
        }
        self.parent[x]
    }

    fn union(&mut self, a: usize, b: usize) -> bool {
        let mut a = self.find(a);
        let mut b = self.find(b);
        if a == b {
            return false;
        }
        if self.rank[a] < self.rank[b] {
            std::mem::swap(&mut a, &mut b);
        }
        self.parent[b] = a;
        if self.rank[a] == self.rank[b] {
            self.rank[a] += 1;
        }
        true
    }
}

fn forced_primal_is_acyclic(grid: &Grid, y: &[bool]) -> bool {
    let mut dsu = Dsu::new(grid.n * grid.n);
    grid.edges
        .iter()
        .enumerate()
        .filter(|(id, _)| !y[*id])
        .all(|(_, edge)| dsu.union(edge.a, edge.b))
}

fn verify_model(config: &Config, grid: &Grid, model: &SatModel) -> Result<(), String> {
    let u_count = model.u.iter().filter(|&&value| value).count();
    if u_count != config.u_count {
        return Err(format!("U count is {u_count}, expected {}", config.u_count));
    }
    for (id, edge) in grid.edges.iter().enumerate() {
        let expected = model.u[edge.a] && model.u[edge.b];
        if model.y[id] != expected {
            return Err(format!("edge {id} violates y <-> (x_a AND x_b)"));
        }
    }
    let edge_count = model.y.iter().filter(|&&value| value).count();
    if config.edge_min.is_some_and(|min| edge_count < min) {
        return Err(format!("eligible edge count {edge_count} is below minimum"));
    }
    if config.edge_max.is_some_and(|max| edge_count > max) {
        return Err(format!("eligible edge count {edge_count} is above maximum"));
    }
    if dual_components(grid, &model.y).1 != 1 {
        return Err("full dual is disconnected".into());
    }
    if !forced_primal_is_acyclic(grid, &model.y) {
        return Err("forced primal edge set has a cycle".into());
    }
    let tree = completed_primal_tree(grid, &model.y)?;
    verify_primal_tree(grid, &tree)?;
    Ok(())
}

fn completed_primal_tree(grid: &Grid, y: &[bool]) -> Result<Vec<usize>, String> {
    let mut adjacency = vec![Vec::<(usize, usize)>::new(); grid.dual_node_count()];
    for (id, edge) in grid.edges.iter().enumerate() {
        if y[id] {
            adjacency[edge.dual_a].push((edge.dual_b, id));
            adjacency[edge.dual_b].push((edge.dual_a, id));
        }
    }
    let mut seen = vec![false; adjacency.len()];
    let mut omitted = vec![false; grid.edges.len()];
    seen[grid.out] = true;
    let mut queue = VecDeque::from([grid.out]);
    while let Some(node) = queue.pop_front() {
        for &(next, edge_id) in &adjacency[node] {
            if !seen[next] {
                seen[next] = true;
                omitted[edge_id] = true;
                queue.push_back(next);
            }
        }
    }
    if seen.iter().any(|value| !value) {
        return Err("cannot complete witness from a disconnected dual".into());
    }
    Ok((0..grid.edges.len()).filter(|&id| !omitted[id]).collect())
}

fn verify_primal_tree(grid: &Grid, tree: &[usize]) -> Result<(), String> {
    let vertices = grid.n * grid.n;
    if tree.len() + 1 != vertices {
        return Err(format!(
            "completed primal graph has {} edges, expected {}",
            tree.len(),
            vertices.saturating_sub(1)
        ));
    }
    let mut dsu = Dsu::new(vertices);
    for &id in tree {
        let edge = grid.edges[id];
        if !dsu.union(edge.a, edge.b) {
            return Err("completed primal graph contains a cycle".into());
        }
    }
    Ok(())
}

fn witness_text(config: &Config, result: &SearchResult) -> Result<String, String> {
    let model = result.model.as_ref().ok_or("result has no witness")?;
    let grid = Grid::new(config.n);
    let tree = completed_primal_tree(&grid, &model.y)?;
    let mut output = String::new();
    writeln!(
        output,
        "# search_n17_sat n={} u_count={} eligible_edges={} tree_edges={}",
        config.n,
        config.u_count,
        model.y.iter().filter(|&&value| value).count(),
        tree.len()
    )
    .unwrap();
    writeln!(
        output,
        "# cuts static_mode={} static={} lazy={} lazy_component_candidates={} duplicates={} rounds={}",
        config.static_cuts.name(),
        result.stats.static_cut_clauses,
        result.stats.lazy_cut_clauses,
        result.stats.lazy_component_candidates,
        result.stats.duplicate_cuts,
        result.stats.solve_rounds
    )
    .unwrap();
    writeln!(output, "# U pattern (U=non-full, .=full)").unwrap();
    for r in 0..config.n {
        for c in 0..config.n {
            output.push(if model.u[r * config.n + c] { 'U' } else { '.' });
        }
        output.push('\n');
    }
    writeln!(output, "# U vertices: row col").unwrap();
    for (id, &is_u) in model.u.iter().enumerate() {
        if is_u {
            writeln!(output, "U {} {}", id / config.n, id % config.n).unwrap();
        }
    }
    writeln!(
        output,
        "# completed primal spanning-tree edges: r1 c1 r2 c2"
    )
    .unwrap();
    for id in tree {
        let edge = grid.edges[id];
        writeln!(
            output,
            "E {} {} {} {}",
            edge.a / config.n,
            edge.a % config.n,
            edge.b / config.n,
            edge.b % config.n
        )
        .unwrap();
    }
    Ok(output)
}

fn json_escape(value: &str) -> String {
    let mut escaped = String::new();
    for ch in value.chars() {
        match ch {
            '"' => escaped.push_str("\\\""),
            '\\' => escaped.push_str("\\\\"),
            '\n' => escaped.push_str("\\n"),
            '\r' => escaped.push_str("\\r"),
            '\t' => escaped.push_str("\\t"),
            ch if ch.is_control() => write!(escaped, "\\u{:04x}", ch as u32).unwrap(),
            ch => escaped.push(ch),
        }
    }
    escaped
}

fn result_json(config: &Config, result: &SearchResult) -> String {
    let eligible_edges = result
        .model
        .as_ref()
        .map(|model| model.y.iter().filter(|&&value| value).count());
    let message = result
        .message
        .as_deref()
        .map(|value| format!("\"{}\"", json_escape(value)))
        .unwrap_or_else(|| "null".into());
    let edge_min = config.edge_min.map_or("null".into(), |v| v.to_string());
    let edge_max = config.edge_max.map_or("null".into(), |v| v.to_string());
    let eligible_edges = eligible_edges.map_or("null".into(), |v| v.to_string());
    let near_hint_cardinality_matches_target = config.near_hint.as_ref().map_or("null", |_| {
        if result.stats.near_hint_cardinality_matches_target {
            "true"
        } else {
            "false"
        }
    });
    format!(
        concat!(
            "{{\n  \"status\": \"{}\",\n  \"n\": {},\n  \"u_count\": {},\n",
            "  \"edge_min\": {},\n  \"edge_max\": {},\n  \"eligible_edges\": {},\n",
            "  \"static_cuts\": \"{}\",\n  \"symmetry\": \"{}\",\n",
            "  \"connectivity\": \"{}\",\n  \"cardinality\": \"{}\",\n",
            "  \"elapsed_seconds\": {:.6},\n",
            "  \"seed_requested\": {},\n  \"near_hint_requested\": {},\n",
            "  \"hint_exchanges\": {},\n",
            "  \"near_hint_cardinality_matches_target\": {},\n",
            "  \"time_limit_soft_between_rounds\": true,\n  \"message\": {},\n  \"stats\": {{\n",
            "    \"base_variables\": {},\n    \"total_variables\": {},\n",
            "    \"base_clauses\": {},\n    \"static_cut_candidates\": {},\n",
            "    \"static_cut_clauses\": {},\n    \"seeded_cut_candidates\": {},\n",
            "    \"seeded_cut_clauses\": {},\n    \"seeded_cut_duplicates\": {},\n",
            "    \"solve_rounds\": {},\n",
            "    \"disconnected_models\": {},\n    \"lazy_component_candidates\": {},\n",
            "    \"lazy_cut_clauses\": {},\n    \"duplicate_cuts\": {}\n  }}\n}}\n"
        ),
        result.status.name(),
        config.n,
        config.u_count,
        edge_min,
        edge_max,
        eligible_edges,
        config.static_cuts.name(),
        config.symmetry.name(),
        config.connectivity.name(),
        config.cardinality.name(),
        result.elapsed.as_secs_f64(),
        config.seed.map_or("null".into(), |v| v.to_string()),
        config
            .near_hint
            .as_ref()
            .map(|v| format!("\"{}\"", json_escape(&v.display().to_string())))
            .unwrap_or_else(|| "null".into()),
        config
            .hint_exchanges
            .map_or("null".into(), |value| value.to_string()),
        near_hint_cardinality_matches_target,
        message,
        result.stats.base_variables,
        result.stats.total_variables,
        result.stats.base_clauses,
        result.stats.static_cut_candidates,
        result.stats.static_cut_clauses,
        result.stats.seeded_cut_candidates,
        result.stats.seeded_cut_clauses,
        result.stats.seeded_cut_duplicates,
        result.stats.solve_rounds,
        result.stats.disconnected_models,
        result.stats.lazy_component_candidates,
        result.stats.lazy_cut_clauses,
        result.stats.duplicate_cuts,
    )
}

fn import_result(
    config: &Config,
    near_hint: Option<&[bool]>,
    contents: &str,
) -> Result<SearchResult, String> {
    let start = Instant::now();
    let problem = build_problem(config, near_hint);
    let u = parse_competition_model(contents, &problem.x)?;
    if config.symmetry == Symmetry::D4 && !is_d4_canonical(&u, config.n) {
        return Err("imported model violates the requested D4 lex leader".into());
    }
    let model = SatModel {
        y: induced_y(&problem.grid, &u),
        u,
    };
    verify_model(config, &problem.grid, &model)
        .map_err(|message| format!("imported model verification failed: {message}"))?;
    Ok(SearchResult {
        status: Status::Witness,
        model: Some(model),
        stats: problem.stats,
        elapsed: start.elapsed(),
        message: Some("validated imported competition-format model".into()),
    })
}

fn run() -> Result<i32, String> {
    let config = Config::parse()?;
    let near_hint = config
        .near_hint
        .as_ref()
        .map(|path| {
            let contents = fs::read_to_string(path)
                .map_err(|error| format!("failed to read near-hint {}: {error}", path.display()))?;
            parse_near_hint(&contents, config.n)
                .map_err(|error| format!("invalid near-hint {}: {error}", path.display()))
        })
        .transpose()?;
    if let (Some(hint), Some(_)) = (near_hint.as_deref(), config.hint_exchanges) {
        let hint_count = hint.iter().filter(|&&is_u| is_u).count();
        if hint_count != config.u_count {
            return Err(format!(
                "--hint-exchanges requires a same-cardinality hint: hint has {hint_count} U vertices, target is {}",
                config.u_count
            ));
        }
    }
    if let Some(path) = &config.output {
        match fs::remove_file(path) {
            Ok(()) => {}
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(error) => {
                return Err(format!(
                    "failed to clear witness output {}: {error}",
                    path.display()
                ));
            }
        }
    }
    if let Some(path) = &config.dimacs_out {
        let problem = build_problem(&config, near_hint.as_deref());
        let file = fs::File::create(path)
            .map_err(|error| format!("failed to create DIMACS {}: {error}", path.display()))?;
        let mut writer = BufWriter::new(file);
        write_dimacs(&mut writer, &problem.formula)
            .map_err(|error| format!("failed to write DIMACS {}: {error}", path.display()))?;
        eprintln!(
            "# wrote DIMACS {} variables={} clauses={} symmetry={}",
            path.display(),
            problem.formula.var_count(),
            problem.formula.len(),
            config.symmetry.name()
        );
        return Ok(0);
    }
    let result = if let Some(path) = &config.model_in {
        let contents = fs::read_to_string(path)
            .map_err(|error| format!("failed to read model {}: {error}", path.display()))?;
        import_result(&config, near_hint.as_deref(), &contents)?
    } else {
        search(&config, near_hint.as_deref())
    };
    eprintln!(
        "# status={} rounds={} static_cuts={} lazy_cuts={} duplicates={} elapsed={:.3}s",
        result.status.name(),
        result.stats.solve_rounds,
        result.stats.static_cut_clauses,
        result.stats.lazy_cut_clauses,
        result.stats.duplicate_cuts,
        result.elapsed.as_secs_f64()
    );
    if let Some(message) = &result.message {
        eprintln!("# {message}");
    }
    if result.status == Status::Witness {
        let witness = witness_text(&config, &result)?;
        if let Some(path) = &config.output {
            fs::write(path, witness)
                .map_err(|error| format!("failed to write witness {}: {error}", path.display()))?;
        } else {
            print!("{witness}");
        }
    }
    if let Some(path) = &config.json {
        fs::write(path, result_json(&config, &result))
            .map_err(|error| format!("failed to write JSON {}: {error}", path.display()))?;
    }
    Ok(result.status.exit_code())
}

fn main() {
    match run() {
        Ok(0) => {}
        Ok(code) => process::exit(code),
        Err(error) => {
            eprintln!("error: {error}");
            eprintln!("try --help for usage");
            process::exit(2);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn solve_formula(mut formula: CnfFormula, assumptions: &[Lit]) -> bool {
        for &lit in assumptions {
            formula.add_clause(&[lit]);
        }
        let mut solver = Solver::new();
        solver.add_formula(&formula);
        solver.solve().unwrap()
    }

    #[test]
    fn and_encoding_has_exact_truth_table() {
        for a_value in [false, true] {
            for b_value in [false, true] {
                for y_value in [false, true] {
                    let mut formula = CnfFormula::new();
                    let a = formula.new_var();
                    let b = formula.new_var();
                    let y = formula.new_var();
                    encode_and(&mut formula, y, a, b);
                    let assumptions = [a.lit(a_value), b.lit(b_value), y.lit(y_value)];
                    assert_eq!(
                        solve_formula(formula, &assumptions),
                        y_value == (a_value && b_value)
                    );
                }
            }
        }
    }

    #[test]
    fn cardinality_matches_brute_force() {
        for n in 0..=6 {
            for k in 0..=n {
                for mask in 0usize..1usize << n {
                    for kind in 0..3 {
                        let mut formula = CnfFormula::new();
                        let vars: Vec<Var> = formula.new_var_iter(n).collect();
                        let lits: Vec<Lit> = vars.iter().map(|v| v.positive()).collect();
                        match kind {
                            0 => encode_at_most(&mut formula, &lits, k),
                            1 => encode_at_least(&mut formula, &lits, k),
                            _ => encode_exactly(&mut formula, &lits, k),
                        }
                        let assumptions: Vec<Lit> = vars
                            .iter()
                            .enumerate()
                            .map(|(i, v)| v.lit(mask & (1 << i) != 0))
                            .collect();
                        let count = mask.count_ones() as usize;
                        let expected = match kind {
                            0 => count <= k,
                            1 => count >= k,
                            _ => count == k,
                        };
                        assert_eq!(
                            solve_formula(formula, &assumptions),
                            expected,
                            "kind={kind} n={n} k={k} mask={mask:b}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn dual_edge_mapping_is_correct() {
        let grid = Grid::new(3);
        assert_eq!(grid.face_count, 4);
        assert_eq!(grid.out, 4);
        assert_eq!(grid.edges.len(), 12);
        assert_eq!((grid.edges[0].dual_a, grid.edges[0].dual_b), (4, 0));
        assert_eq!((grid.edges[2].dual_a, grid.edges[2].dual_b), (0, 2));
        assert_eq!((grid.edges[4].dual_a, grid.edges[4].dual_b), (2, 4));
        assert_eq!((grid.edges[6].dual_a, grid.edges[6].dual_b), (4, 0));
        assert_eq!((grid.edges[7].dual_a, grid.edges[7].dual_b), (0, 1));
        assert_eq!((grid.edges[8].dual_a, grid.edges[8].dual_b), (1, 4));
    }

    #[test]
    fn every_static_cut_is_valid_for_connected_tiny_patterns() {
        for n in 1..=3 {
            let grid = Grid::new(n);
            for mask in 0usize..1usize << grid.edges.len() {
                let y: Vec<bool> = (0..grid.edges.len())
                    .map(|id| mask & (1 << id) != 0)
                    .collect();
                if dual_components(&grid, &y).1 != 1 {
                    continue;
                }
                for mode in [
                    StaticCuts::Singleton,
                    StaticCuts::Interval,
                    StaticCuts::SmallRect,
                    StaticCuts::AllRect,
                ] {
                    for spec in rectangle_specs(&grid, mode) {
                        let cut = rectangle_cut(&grid, spec);
                        assert!(cut.iter().any(|&id| y[id]), "n={n} mode={mode:?}");
                    }
                }
            }
        }
    }

    fn brute_feasible(n: usize, u_count: usize, edge_count: Option<usize>) -> bool {
        let grid = Grid::new(n);
        (0usize..1usize << (n * n)).any(|mask| {
            if mask.count_ones() as usize != u_count {
                return false;
            }
            let y: Vec<bool> = grid
                .edges
                .iter()
                .map(|edge| mask & (1 << edge.a) != 0 && mask & (1 << edge.b) != 0)
                .collect();
            dual_components(&grid, &y).1 == 1
                && edge_count.is_none_or(|count| y.iter().filter(|&&value| value).count() == count)
        })
    }

    #[test]
    fn solver_agrees_with_brute_force_through_n4() {
        for n in 1..=4 {
            for u_count in 0..=n * n {
                let config = Config {
                    n,
                    u_count,
                    edge_min: None,
                    edge_max: None,
                    static_cuts: StaticCuts::Singleton,
                    symmetry: Symmetry::None,
                    connectivity: Connectivity::Rooted,
                    cardinality: Cardinality::Binary,
                    time_limit: None,
                    seed: None,
                    near_hint: None,
                    hint_exchanges: None,
                    output: None,
                    json: None,
                    dimacs_out: None,
                    model_in: None,
                    max_rounds: 10_000,
                };
                let result = search(&config, None);
                assert!(matches!(result.status, Status::Witness | Status::Unsat));
                assert_eq!(
                    result.status == Status::Witness,
                    brute_feasible(n, u_count, None),
                    "n={n} u_count={u_count}"
                );
            }
        }
    }

    #[test]
    fn exact_edge_bounds_agree_with_brute_force_through_n3() {
        for n in 1..=3 {
            let edge_count_max = 2 * n * (n - 1);
            for u_count in 0..=n * n {
                for edge_count in 0..=edge_count_max {
                    for connectivity in [Connectivity::Rooted, Connectivity::Lazy] {
                        for cardinality in [Cardinality::Binary, Cardinality::Sequential] {
                            let config = Config {
                                n,
                                u_count,
                                edge_min: Some(edge_count),
                                edge_max: Some(edge_count),
                                static_cuts: StaticCuts::Singleton,
                                symmetry: Symmetry::None,
                                connectivity,
                                cardinality,
                                time_limit: None,
                                seed: None,
                                near_hint: None,
                                hint_exchanges: None,
                                output: None,
                                json: None,
                                dimacs_out: None,
                                model_in: None,
                                max_rounds: 10_000,
                            };
                            let result = search(&config, None);
                            assert_eq!(
                                result.status == Status::Witness,
                                brute_feasible(n, u_count, Some(edge_count)),
                                "n={n} u_count={u_count} edge_count={edge_count} connectivity={connectivity:?} cardinality={cardinality:?}"
                            );
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn lazy_sequential_solver_agrees_with_brute_force_through_n3() {
        for n in 1..=3 {
            for u_count in 0..=n * n {
                let config = Config {
                    n,
                    u_count,
                    edge_min: None,
                    edge_max: None,
                    static_cuts: StaticCuts::Interval,
                    symmetry: Symmetry::None,
                    connectivity: Connectivity::Lazy,
                    cardinality: Cardinality::Sequential,
                    time_limit: None,
                    seed: None,
                    near_hint: None,
                    hint_exchanges: None,
                    output: None,
                    json: None,
                    dimacs_out: None,
                    model_in: None,
                    max_rounds: 10_000,
                };
                let result = search(&config, None);
                assert_eq!(
                    result.status == Status::Witness,
                    brute_feasible(n, u_count, None),
                    "n={n} u_count={u_count}"
                );
            }
        }
    }

    #[test]
    fn near_hint_parser_accepts_plain_and_repository_witness_patterns() {
        let expected = vec![true, false, false, false, true, false, false, false, true];
        assert_eq!(parse_near_hint("U..\n.U.\n..U\n", 3).unwrap(), expected);

        let witness = "# search metadata\n# U pattern (U=non-full, .=full)\n\
                       U..\n.U.\n..U\n# U vertices: row col\nU 0 0\nU 1 1\n\
                       # completed primal spanning-tree edges\nE 0 0 0 1\n";
        assert_eq!(parse_near_hint(witness, 3).unwrap(), expected);
    }

    #[test]
    fn near_hint_parser_validates_rows_and_dimensions() {
        assert!(parse_near_hint("U.\n..\n", 3).is_err());
        assert!(parse_near_hint("...\n...\n", 3).is_err());
        assert!(parse_near_hint("...\n.X.\n...\n", 3).is_err());
    }

    #[test]
    fn near_hint_component_cuts_are_valid_and_reject_the_hint_model() {
        let grid = Grid::new(3);
        let hint = parse_near_hint("...\n...\n...\n", 3).unwrap();
        let hint_y = induced_y(&grid, &hint);
        let cuts = near_hint_cuts(&grid, &hint);
        assert!(!cuts.is_empty());

        for mask in 0usize..1usize << grid.edges.len() {
            let candidate_y: Vec<bool> = (0..grid.edges.len())
                .map(|id| mask & (1 << id) != 0)
                .collect();
            if dual_components(&grid, &candidate_y).1 == 1 {
                for cut in &cuts {
                    assert!(cut.iter().any(|&id| candidate_y[id]));
                }
            }
        }

        let mut formula = CnfFormula::new();
        let y: Vec<Var> = formula.new_var_iter(grid.edges.len()).collect();
        for cut in cuts {
            formula.add_clause(&cut.iter().map(|&id| y[id].positive()).collect::<Vec<_>>());
        }
        let assumptions: Vec<Lit> = y
            .iter()
            .zip(hint_y)
            .map(|(var, value)| var.lit(value))
            .collect();
        assert!(!solve_formula(formula, &assumptions));
    }

    #[test]
    fn separation_cuts_reject_every_disconnected_tiny_model() {
        for n in 2..=3 {
            let grid = Grid::new(n);
            for mask in 0usize..1usize << grid.edges.len() {
                let y: Vec<bool> = (0..grid.edges.len())
                    .map(|id| mask & (1 << id) != 0)
                    .collect();
                let (components, component_count) = dual_components(&grid, &y);
                if component_count == 1 {
                    continue;
                }
                let cuts = separation_cuts(&grid, &components, component_count);
                assert!(!cuts.is_empty());
                for cut in cuts {
                    assert!(!cut.is_empty());
                    assert!(cut.iter().all(|&edge| !y[edge]));
                }
            }
        }
    }

    #[test]
    fn small_rect_includes_rectangles_with_side_four() {
        let grid = Grid::new(6);
        let specs = rectangle_specs(&grid, StaticCuts::SmallRect);
        assert!(specs.contains(&(0, 4, 0, 1)));
        assert!(specs.contains(&(0, 1, 0, 4)));
        assert!(specs.contains(&(0, 4, 0, 4)));
        assert!(!specs.contains(&(0, 5, 0, 1)));
        assert!(!specs.contains(&(0, 1, 0, 5)));
    }

    #[test]
    fn statuses_have_stable_exit_codes() {
        assert_eq!(Status::Witness.exit_code(), 0);
        assert_eq!(Status::Unsat.exit_code(), 0);
        assert_eq!(Status::TimeLimit.exit_code(), 3);
        assert_eq!(Status::MaxRounds.exit_code(), 3);
        assert_eq!(Status::SolverError.exit_code(), 4);
    }

    #[test]
    fn d4_transforms_are_permutations() {
        for n in 1..=6 {
            for transform in 0..8 {
                let mut indices: Vec<usize> = (0..n * n)
                    .map(|index| d4_source_index(n, transform, index))
                    .collect();
                indices.sort_unstable();
                assert_eq!(indices, (0..n * n).collect::<Vec<_>>());
            }
        }
    }

    #[test]
    fn lex_leaders_match_direct_comparison_through_n3() {
        for n in 1..=3 {
            for transform in 1..8 {
                for mask in 0usize..1usize << (n * n) {
                    let mut formula = CnfFormula::new();
                    let x: Vec<Var> = formula.new_var_iter(n * n).collect();
                    let transformed: Vec<Var> = (0..x.len())
                        .map(|index| x[d4_source_index(n, transform, index)])
                        .collect();
                    encode_lex_leader(&mut formula, &x, &transformed);
                    let assumptions: Vec<Lit> = x
                        .iter()
                        .enumerate()
                        .map(|(index, var)| var.lit(mask & (1 << index) != 0))
                        .collect();
                    let direct = (0..x.len())
                        .map(|index| {
                            (mask & (1 << index) != 0)
                                .cmp(&(mask & (1 << d4_source_index(n, transform, index)) != 0))
                        })
                        .find(|ordering| !ordering.is_eq())
                        .is_none_or(|ordering| ordering.is_lt());
                    assert_eq!(solve_formula(formula, &assumptions), direct);
                }
            }
        }
    }

    #[test]
    fn d4_encoding_keeps_exactly_canonical_assignments_through_n3() {
        for n in 1..=3 {
            for mask in 0usize..1usize << (n * n) {
                let mut formula = CnfFormula::new();
                let x: Vec<Var> = formula.new_var_iter(n * n).collect();
                encode_d4_symmetry(&mut formula, &x, n);
                let assumptions: Vec<Lit> = x
                    .iter()
                    .enumerate()
                    .map(|(index, var)| var.lit(mask & (1 << index) != 0))
                    .collect();
                let values: Vec<bool> = (0..n * n).map(|index| mask & (1 << index) != 0).collect();
                assert_eq!(
                    solve_formula(formula, &assumptions),
                    is_d4_canonical(&values, n)
                );
            }
        }
    }

    #[test]
    fn competition_model_parser_handles_wrapping_and_rejects_bad_models() {
        let mut formula = CnfFormula::new();
        let vars: Vec<Var> = formula.new_var_iter(3).collect();
        assert_eq!(
            parse_competition_model("c model\ns SATISFIABLE\nv 1 -2\nv 3 0\n", &vars).unwrap(),
            vec![true, false, true]
        );
        assert!(parse_competition_model("s UNSATISFIABLE\n", &vars).is_err());
        assert!(parse_competition_model("s SATISFIABLE\nv 1 -2 0\n", &vars).is_err());
        assert!(parse_competition_model("s SATISFIABLE\nv 1 -1 -2 3 0\n", &vars).is_err());
    }
}
