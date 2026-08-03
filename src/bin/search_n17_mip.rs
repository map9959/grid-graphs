//! Export and independently validate a global dual-connectivity flow MIP.

use std::collections::VecDeque;
use std::env;
use std::fmt::Write as _;
use std::fs;
use std::io::{BufWriter, Write};
use std::path::PathBuf;
use std::process;

#[derive(Debug)]
struct Config {
    n: usize,
    u_count: usize,
    model_out: Option<PathBuf>,
    solution_in: Option<PathBuf>,
    witness_out: Option<PathBuf>,
}

impl Config {
    fn parse() -> Result<Self, String> {
        let mut n = None;
        let mut u_count = None;
        let mut model_out = None;
        let mut solution_in = None;
        let mut witness_out = None;
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
                "--model-out" => model_out = Some(PathBuf::from(value)),
                "--solution-in" => solution_in = Some(PathBuf::from(value)),
                "--witness-out" => witness_out = Some(PathBuf::from(value)),
                _ => return Err(format!("unknown option {flag:?}")),
            }
        }
        let config = Self {
            n: n.ok_or("--n is required")?,
            u_count: u_count.ok_or("--u-count is required")?,
            model_out,
            solution_in,
            witness_out,
        };
        if config.n < 2 {
            return Err("--n must be at least 2".into());
        }
        if config.u_count > config.n * config.n {
            return Err(format!("--u-count cannot exceed {}", config.n * config.n));
        }
        if config.model_out.is_none() && config.solution_in.is_none() {
            return Err("at least one of --model-out or --solution-in is required".into());
        }
        if config.witness_out.is_some() && config.solution_in.is_none() {
            return Err("--witness-out requires --solution-in".into());
        }
        Ok(config)
    }
}

fn parse_usize(flag: &str, value: &str) -> Result<usize, String> {
    value
        .parse()
        .map_err(|_| format!("invalid integer for {flag}: {value:?}"))
}

fn print_usage() {
    eprintln!(
        "Usage: search_n17_mip --n N --u-count K [options]\n\
         Options:\n\
           --model-out PATH       export deterministic CPLEX LP model\n\
           --solution-in PATH     validate a HiGHS solution independently\n\
           --witness-out PATH     write validated U pattern"
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
    edges: Vec<PrimalEdge>,
    face_count: usize,
    out: usize,
}

impl Grid {
    fn new(n: usize) -> Self {
        let side = n - 1;
        let face_count = side * side;
        let out = face_count;
        let face = |r: usize, c: usize| r * side + c;
        let mut edges = Vec::with_capacity(2 * n * side);
        for r in 0..n {
            for c in 0..side {
                edges.push(PrimalEdge {
                    a: r * n + c,
                    b: r * n + c + 1,
                    dual_a: if r == 0 { out } else { face(r - 1, c) },
                    dual_b: if r == side { out } else { face(r, c) },
                });
            }
        }
        for r in 0..side {
            for c in 0..n {
                edges.push(PrimalEdge {
                    a: r * n + c,
                    b: (r + 1) * n + c,
                    dual_a: if c == 0 { out } else { face(r, c - 1) },
                    dual_b: if c == side { out } else { face(r, c) },
                });
            }
        }
        Self {
            edges,
            face_count,
            out,
        }
    }

    fn dual_node_count(&self) -> usize {
        self.face_count + 1
    }
}

fn x_name(index: usize) -> String {
    format!("x_{index}")
}

fn y_name(edge: usize) -> String {
    format!("y_{edge}")
}

fn f_name(edge: usize, direction: usize) -> String {
    format!("f_{edge}_{direction}")
}

fn linear_expression(terms: &[(i64, String)]) -> String {
    let mut output = String::new();
    for (index, (coefficient, variable)) in terms.iter().enumerate() {
        if index == 0 {
            if *coefficient < 0 {
                output.push_str("- ");
            }
        } else if *coefficient < 0 {
            output.push_str(" - ");
        } else {
            output.push_str(" + ");
        }
        let magnitude = coefficient.unsigned_abs();
        if magnitude != 1 {
            write!(output, "{magnitude} ").unwrap();
        }
        output.push_str(variable);
    }
    if terms.is_empty() {
        output.push('0');
    }
    output
}

fn export_lp(config: &Config, grid: &Grid, path: &PathBuf) -> Result<(), String> {
    let file = fs::File::create(path)
        .map_err(|error| format!("failed to create {}: {error}", path.display()))?;
    let mut out = BufWriter::new(file);
    writeln!(
        out,
        "\\ global dual-connectivity flow MIP, n={}, |U|={}",
        config.n, config.u_count
    )
    .unwrap();
    writeln!(out, "Minimize\n obj: 0\nSubject To").unwrap();

    let cardinality: Vec<_> = (0..config.n * config.n)
        .map(|vertex| (1, x_name(vertex)))
        .collect();
    writeln!(
        out,
        " cardinality: {} = {}",
        linear_expression(&cardinality),
        config.u_count
    )
    .unwrap();

    for (id, edge) in grid.edges.iter().enumerate() {
        writeln!(
            out,
            " prod_a_{id}: {} - {} <= 0",
            y_name(id),
            x_name(edge.a)
        )
        .unwrap();
        writeln!(
            out,
            " prod_b_{id}: {} - {} <= 0",
            y_name(id),
            x_name(edge.b)
        )
        .unwrap();
        writeln!(
            out,
            " prod_lb_{id}: {} - {} - {} >= -1",
            y_name(id),
            x_name(edge.a),
            x_name(edge.b)
        )
        .unwrap();
        for direction in 0..2 {
            writeln!(
                out,
                " capacity_{id}_{direction}: {} - {} {} <= 0",
                f_name(id, direction),
                grid.face_count,
                y_name(id)
            )
            .unwrap();
        }
    }

    for node in 0..grid.dual_node_count() {
        let mut terms = Vec::new();
        for (id, edge) in grid.edges.iter().enumerate() {
            if edge.dual_a == node {
                terms.push((1, f_name(id, 0)));
                terms.push((-1, f_name(id, 1)));
            } else if edge.dual_b == node {
                terms.push((1, f_name(id, 1)));
                terms.push((-1, f_name(id, 0)));
            }
        }
        let rhs = if node == grid.out {
            grid.face_count as i64
        } else {
            -1
        };
        writeln!(out, " flow_{node}: {} = {rhs}", linear_expression(&terms)).unwrap();
    }

    for face in 0..grid.face_count {
        let incident: Vec<_> = grid
            .edges
            .iter()
            .enumerate()
            .filter(|(_, edge)| edge.dual_a == face || edge.dual_b == face)
            .map(|(id, _)| (1, y_name(id)))
            .collect();
        writeln!(
            out,
            " singleton_{face}: {} >= 1",
            linear_expression(&incident)
        )
        .unwrap();
    }
    let active_edges: Vec<_> = (0..grid.edges.len()).map(|id| (1, y_name(id))).collect();
    writeln!(
        out,
        " edge_rank: {} >= {}",
        linear_expression(&active_edges),
        grid.face_count
    )
    .unwrap();

    writeln!(out, "Bounds").unwrap();
    for id in 0..grid.edges.len() {
        writeln!(out, " 0 <= {} <= 1", y_name(id)).unwrap();
        writeln!(out, " 0 <= {} <= {}", f_name(id, 0), grid.face_count).unwrap();
        writeln!(out, " 0 <= {} <= {}", f_name(id, 1), grid.face_count).unwrap();
    }
    writeln!(out, "Binary").unwrap();
    for vertex in 0..config.n * config.n {
        writeln!(out, " {}", x_name(vertex)).unwrap();
    }
    writeln!(out, "End").unwrap();
    out.flush()
        .map_err(|error| format!("failed to write {}: {error}", path.display()))?;
    Ok(())
}

fn parse_solution(contents: &str, vertices: usize) -> Result<Vec<bool>, String> {
    let lower = contents.to_ascii_lowercase();
    if lower.contains("model status\ninfeasible") || lower.contains("model status\r\ninfeasible") {
        return Err("solution reports an infeasible model; there is no witness to validate".into());
    }
    let mut values = vec![None; vertices];
    for (line_index, line) in contents.lines().enumerate() {
        let mut fields = line.split_whitespace();
        let Some(name) = fields.next() else {
            continue;
        };
        let Some(index_text) = name.strip_prefix("x_") else {
            continue;
        };
        let index = index_text.parse::<usize>().map_err(|_| {
            format!(
                "invalid x variable name {name:?} on line {}",
                line_index + 1
            )
        })?;
        if index >= vertices {
            continue;
        }
        let value_text = fields
            .next()
            .ok_or_else(|| format!("missing value for {name} on line {}", line_index + 1))?;
        let value = value_text.parse::<f64>().map_err(|_| {
            format!(
                "invalid value {value_text:?} for {name} on line {}",
                line_index + 1
            )
        })?;
        if (value - value.round()).abs() > 1e-6 || !(0.0..=1.0).contains(&value) {
            return Err(format!("non-binary value {value} for {name}"));
        }
        let value = value >= 0.5;
        if values[index]
            .replace(value)
            .is_some_and(|prior| prior != value)
        {
            return Err(format!("conflicting values for {name}"));
        }
    }
    values
        .into_iter()
        .enumerate()
        .map(|(index, value)| value.ok_or_else(|| format!("solution omits {}", x_name(index))))
        .collect()
}

fn induced_edges(grid: &Grid, u: &[bool]) -> Vec<bool> {
    grid.edges
        .iter()
        .map(|edge| u[edge.a] && u[edge.b])
        .collect()
}

fn dual_is_connected(grid: &Grid, active: &[bool]) -> bool {
    let mut adjacency = vec![Vec::new(); grid.dual_node_count()];
    for (id, edge) in grid.edges.iter().enumerate() {
        if active[id] {
            adjacency[edge.dual_a].push(edge.dual_b);
            adjacency[edge.dual_b].push(edge.dual_a);
        }
    }
    let mut seen = vec![false; adjacency.len()];
    seen[grid.out] = true;
    let mut queue = VecDeque::from([grid.out]);
    while let Some(node) = queue.pop_front() {
        for &next in &adjacency[node] {
            if !seen[next] {
                seen[next] = true;
                queue.push_back(next);
            }
        }
    }
    seen.into_iter().all(|value| value)
}

fn validate_solution(config: &Config, grid: &Grid, contents: &str) -> Result<Vec<bool>, String> {
    let u = parse_solution(contents, config.n * config.n)?;
    let count = u.iter().filter(|&&value| value).count();
    if count != config.u_count {
        return Err(format!(
            "solution has {count} U vertices, expected {}",
            config.u_count
        ));
    }
    let active = induced_edges(grid, &u);
    if !dual_is_connected(grid, &active) {
        return Err("induced dual graph is disconnected".into());
    }
    Ok(u)
}

fn witness_text(config: &Config, grid: &Grid, u: &[bool]) -> String {
    let active = induced_edges(grid, u);
    let mut output = format!(
        "# search_n17_mip n={} u_count={} eligible_edges={}\n",
        config.n,
        config.u_count,
        active.iter().filter(|&&value| value).count()
    );
    for row in 0..config.n {
        for col in 0..config.n {
            output.push(if u[row * config.n + col] { 'U' } else { '.' });
        }
        output.push('\n');
    }
    output
}

fn run() -> Result<(), String> {
    let config = Config::parse()?;
    let grid = Grid::new(config.n);
    if let Some(path) = &config.model_out {
        export_lp(&config, &grid, path)?;
        eprintln!(
            "exported {}: x_binary={} y_continuous={} flow_continuous={}",
            path.display(),
            config.n * config.n,
            grid.edges.len(),
            2 * grid.edges.len()
        );
    }
    if let Some(path) = &config.solution_in {
        let contents = fs::read_to_string(path)
            .map_err(|error| format!("failed to read {}: {error}", path.display()))?;
        let u = validate_solution(&config, &grid, &contents)?;
        let witness = witness_text(&config, &grid, &u);
        if let Some(output) = &config.witness_out {
            fs::write(output, &witness)
                .map_err(|error| format!("failed to write {}: {error}", output.display()))?;
        }
        print!("{witness}");
    }
    Ok(())
}

fn main() {
    if let Err(message) = run() {
        eprintln!("error: {message}");
        process::exit(2);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dual_edge_mapping_matches_sat_model() {
        let grid = Grid::new(3);
        assert_eq!(grid.face_count, 4);
        assert_eq!((grid.edges[0].dual_a, grid.edges[0].dual_b), (4, 0));
        assert_eq!((grid.edges[2].dual_a, grid.edges[2].dual_b), (0, 2));
        assert_eq!((grid.edges[4].dual_a, grid.edges[4].dual_b), (2, 4));
        assert_eq!((grid.edges[6].dual_a, grid.edges[6].dual_b), (4, 0));
        assert_eq!((grid.edges[7].dual_a, grid.edges[7].dual_b), (0, 1));
        assert_eq!((grid.edges[8].dual_a, grid.edges[8].dual_b), (1, 4));
    }

    #[test]
    fn parses_highs_style_column_values() {
        let solution = "Model status\nOptimal\n\n# Columns 4\nx_0 1\nx_1 0\nx_2 1\nx_3 0\n";
        assert_eq!(
            parse_solution(solution, 4).unwrap(),
            [true, false, true, false]
        );
    }

    #[test]
    fn all_vertices_connect_the_dual() {
        let grid = Grid::new(4);
        let u = vec![true; 16];
        assert!(dual_is_connected(&grid, &induced_edges(&grid, &u)));
    }
}
