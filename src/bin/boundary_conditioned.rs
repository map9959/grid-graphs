//! Complete fixed-exterior experiments. Output includes all accepted cases.
use grid_graphs::boundary_conditioned::{four_square, moving_seams};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<_> = std::env::args().collect();
    if args.len() != 2 {
        return Err("usage: boundary_conditioned OUTPUT.json".into());
    }
    let four = four_square();
    let seams = moving_seams();
    for (name, cases) in [("four_square", &four), ("moving_seams", &seams)] {
        let tested: u64 = cases.iter().map(|c| c.result.tested).sum();
        let feasible: u64 = cases.iter().map(|c| c.result.feasible).sum();
        let positive = cases
            .iter()
            .filter(|c| c.result.relaxed_optimum > c.result.optimum)
            .count();
        let max_loss = cases
            .iter()
            .map(|c| c.result.relaxed_optimum - c.result.optimum)
            .max()
            .unwrap_or(0);
        println!("{name}: {} feasible baselines, {tested} fillings, {feasible} legal, {positive} positive connectivity prices, max price {max_loss}", cases.len());
    }
    let output = serde_json::json!({
        "schema": 1,
        "scope": "complete specified finite families; all fillings literal-audited; no global upper claim",
        "four_square": four,
        "moving_seams": seams,
    });
    // Do not overwrite a prior frozen result.
    let file = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&args[1])?;
    serde_json::to_writer_pretty(file, &output)?;
    Ok(())
}
