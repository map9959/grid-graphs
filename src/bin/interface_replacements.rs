//! Prespecified replacement shapes on three recorded 14-square boards.
use grid_graphs::boundary_conditioned::Interface;
use grid_graphs::certificate_corpus::{observe, Board};
use serde_json::{json, Value};

fn rectangle(x: usize, y: usize, w: usize, h: usize) -> Vec<usize> {
    (y..y + h)
        .flat_map(|yy| (x..x + w).map(move |xx| yy * 14 + xx))
        .collect()
}

fn regions(trace_support: &[usize]) -> Vec<(String, Vec<usize>)> {
    let mut regions = Vec::new();
    for y in 0..12 {
        for x in 0..12 {
            regions.push((format!("compact_{x}_{y}"), rectangle(x, y, 3, 3)));
        }
    }
    for y in [0, 3, 6, 9] {
        for x in [0, 4, 8, 11] {
            regions.push((format!("strip_{x}_{y}"), rectangle(x, y, 3, 5)));
        }
    }
    let tiles: Vec<_> = [0, 6, 12]
        .into_iter()
        .flat_map(|y| [0, 3, 6, 9].into_iter().map(move |x| rectangle(x, y, 3, 2)))
        .collect();
    for i in 0..tiles.len() {
        for j in i + 1..tiles.len() {
            let mut pair = tiles[i].clone();
            pair.extend(&tiles[j]);
            regions.push((format!("pair_{i}_{j}"), pair));
        }
    }
    // Trace-informed positive controls, explicitly separate from generic shapes.
    regions.push(("control_core".into(), rectangle(2, 5, 3, 4)));
    let mut tether = rectangle(2, 5, 3, 4);
    tether.push(10);
    regions.push(("control_core_boundary".into(), tether));
    regions.push(("control_trace_support".into(), trace_support.to_vec()));
    regions
}

fn run(name: &str, original: &Board, regions: &[(String, Vec<usize>)]) -> Value {
    let original_observation = observe(original).unwrap();
    let mut cases = Vec::new();
    let mut tested = 0;
    let mut improvements = 0;
    for (label, region) in regions {
        let old_optional = region.iter().filter(|&&v| original.preserved[v]).count();
        let mut baseline = original.clone();
        for &v in region {
            baseline.preserved[v] = false;
        }
        let interface = Interface::new(baseline.clone(), region).unwrap();
        let (result, profile) = interface.enumerate_profile(true);
        assert!(result.optimum >= old_optional);
        tested += result.tested;
        if result.optimum > old_optional {
            improvements += 1;
            println!(
                "{name}/{label}: actual gain {}, relaxed gain {}",
                result.optimum - old_optional,
                result.relaxed_optimum - old_optional
            );
        }
        cases.push(json!({
            "name": label, "region": region, "baseline": baseline.rows(),
            "ports": interface.ports, "outside_closed": interface.outside_closed,
            "original_optional": old_optional, "result": result, "rank_profile": profile,
        }));
    }
    println!(
        "{name}: {} complete regions, {tested} fillings, {improvements} improving regions",
        cases.len()
    );
    json!({"name": name, "original": original_observation, "cases": cases})
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<_> = std::env::args().collect();
    if args.len() < 2 || args.len() > 3 || (args.len() == 3 && args[2] != "suppliers") {
        return Err("usage: interface_replacements OUTPUT.json [suppliers]".into());
    }
    // Reserve output before doing the experiment; never overwrite frozen data.
    let file = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&args[1])?;
    let trap = Board::parse(include_str!("../../data/corpus_trap_14.txt"))?;
    let optimum = Board::parse(include_str!("../../data/neutral_escape_14.txt"))?;
    let mut prepared = trap.clone();
    // Exactly the eleven neutral moves in data/neutral_escape_14.json.
    for (delete, add) in [
        (86, 101),
        (75, 73),
        (103, 90),
        (120, 118),
        (108, 121),
        (38, 80),
        (78, 50),
        (104, 91),
        (10, 38),
        (44, 89),
        (87, 72),
    ] {
        assert!(prepared.preserved[delete] && !prepared.preserved[add]);
        prepared.preserved[delete] = false;
        prepared.preserved[add] = true;
        assert_eq!(observe(&prepared)?.features["f"], 76);
    }
    let mut replay = prepared.clone();
    for v in [73, 101] {
        replay.preserved[v] = false;
    }
    for v in [10, 88, 114] {
        replay.preserved[v] = true;
    }
    assert_eq!(replay, optimum);
    let support: Vec<_> = (0..196)
        .filter(|&v| trap.preserved[v] != optimum.preserved[v])
        .collect();
    assert_eq!(support.len(), 19);
    let boards: Vec<_> = if args.len() == 3 {
        let core = rectangle(2, 5, 3, 4);
        let regions: Vec<_> = (0..196)
            .filter(|v| !core.contains(v) && !prepared.preserved[*v])
            .map(|v| {
                let mut region = core.clone();
                region.push(v);
                (format!("supplier_{v}"), region)
            })
            .collect();
        vec![run("prepared76_suppliers", &prepared, &regions)]
    } else {
        let regions = regions(&support);
        [
            ("trap76", &trap),
            ("prepared76", &prepared),
            ("endpoint77", &optimum),
        ]
        .into_iter()
        .map(|(name, board)| run(name, board, &regions))
        .collect()
    };
    serde_json::to_writer_pretty(
        file,
        &json!({
            "schema": 1,
            "scope": "complete listed regions, original exterior fixed; all fillings literal-audited; trace-informed controls are not discoveries",
            "boards": boards,
        }),
    )?;
    Ok(())
}
