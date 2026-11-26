use grid_graphs::certificate_corpus::{observe, Board};
use grid_graphs::terminal_separation::{blocked_terminals, rectangles, scan};
use serde_json::{json, Value};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<_> = std::env::args().collect();
    if args.len() != 2 {
        return Err("usage: terminal_separation OUTPUT.json".into());
    }
    let file = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&args[1])?;
    let recorded: Value =
        serde_json::from_str(include_str!("../../data/interface_replacements_14.json"))?;
    let mut inputs = Vec::new();
    for b in recorded["boards"].as_array().unwrap() {
        let rows: Vec<String> = serde_json::from_value(b["original"]["rows"].clone())?;
        inputs.push((
            b["name"].as_str().unwrap().to_string(),
            Board::parse(&rows.join("\n"))?,
        ));
    }
    for i in 0..8 {
        let path = format!("data/shuffle_study_14/input_{i:02}.txt");
        inputs.push((
            format!("comparison_{i:02}"),
            Board::parse(&std::fs::read_to_string(path)?)?,
        ));
    }
    let mut output = Vec::new();
    for (name, board) in inputs {
        let terminals = blocked_terminals(&board);
        let mut cases = Vec::new();
        for region in rectangles(board.n) {
            cases.push(scan(&board, &region, &terminals)?);
        }
        let tested: u64 = cases.iter().map(|r| r.fillings_tested).sum();
        let pairs: usize = cases.iter().map(|r| r.terminals.len()).sum();
        let severable = cases
            .iter()
            .flat_map(|r| &r.terminals)
            .filter(|t| t.clearing_separates)
            .count();
        let neutral = cases
            .iter()
            .flat_map(|r| &r.terminals)
            .filter(|t| t.neutral_mask.is_some())
            .count();
        println!("{name}: {} terminals, {pairs} compatible core/terminal pairs, {severable} separable by clearing, {neutral} neutral separators, {tested} fillings", terminals.len());
        output.push(json!({"name": name, "original": observe(&board)?, "terminals": terminals, "cases": cases}));
    }
    serde_json::to_writer_pretty(
        file,
        &json!({"schema": 1, "scope": "complete specified cores and single-edge terminals; reused inputs", "boards": output}),
    )?;
    Ok(())
}
