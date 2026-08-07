use std::env;
use std::fs;
use std::io::{self, Read};

use grid_graphs::exact_centered_square::CenteredSquareMonitor;

fn run() -> Result<(), String> {
    let mut args = env::args().skip(1);
    let path = args
        .next()
        .ok_or_else(|| "usage: centered_square_monitor PATTERN|- [--side N]".to_owned())?;
    let mut requested_side = None;
    while let Some(flag) = args.next() {
        match flag.as_str() {
            "--side" => {
                requested_side = Some(
                    args.next()
                        .ok_or("--side requires a value")?
                        .parse::<usize>()
                        .map_err(|error| format!("invalid --side value: {error}"))?,
                );
            }
            _ => return Err(format!("unknown argument {flag:?}")),
        }
    }
    let contents = if path == "-" {
        let mut contents = String::new();
        io::stdin()
            .read_to_string(&mut contents)
            .map_err(|error| format!("failed to read stdin: {error}"))?;
        contents
    } else {
        fs::read_to_string(&path).map_err(|error| format!("failed to read {path}: {error}"))?
    };
    let monitor = CenteredSquareMonitor::parse(&contents)?;
    if let Some(side) = requested_side {
        println!(
            "{}",
            serde_json::to_string_pretty(
                &monitor.profile(side).map_err(|error| error.to_string())?
            )
            .map_err(|error| error.to_string())?
        );
    } else {
        println!(
            "{}",
            serde_json::to_string_pretty(&monitor.profiles()).map_err(|error| error.to_string())?
        );
    }
    Ok(())
}

fn main() {
    if let Err(error) = run() {
        eprintln!("error: {error}");
        std::process::exit(2);
    }
}
