#[allow(dead_code)]
#[path = "search_n17_frontier_pruned.rs"]
mod frontier;

fn main() {
    if let Err(error) = frontier::centered_product_entry() {
        eprintln!("error: {error}");
        std::process::exit(2);
    }
}
