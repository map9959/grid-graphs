use std::fs::File;
use std::io::{BufRead, BufReader};
use std::path::Path;
use plotly::{Plot, Scatter, HeatMap, Layout, common::Mode, layout::Axis};

#[derive(Clone, Debug)]
pub struct Rec { pub m: usize, pub n: usize, pub actual:i32, pub lb_band:i32, pub ub_cap:i32, pub ub_rel:i32 }

pub fn load(csv:&Path) -> anyhow::Result<Vec<Rec>> {
    let f = File::open(csv)?; let mut it = BufReader::new(f).lines();
    let header = it.next().ok_or_else(|| anyhow::anyhow!("empty csv"))??;
    if !header.starts_with("m,n,actual") { return Err(anyhow::anyhow!("unexpected header: {header}")); }
    let mut out = Vec::new();
    for l in it { let l=l?; if l.trim().is_empty() { continue; } let p:Vec<&str>=l.split(',').collect(); if p.len()<7 { continue; }
        out.push(Rec{ m:p[0].parse()?, n:p[1].parse()?, actual:p[2].parse()?, lb_band:p[4].parse()?, ub_cap:p[5].parse()?, ub_rel:p[6].parse()? }); }
    Ok(out)
}

pub fn write_heatmaps(csv:&Path, out_dir:&Path) -> anyhow::Result<()> {
    std::fs::create_dir_all(out_dir)?;
    let recs = load(csv)?;
    let mut ms: Vec<usize> = recs.iter().map(|r| r.m).collect(); ms.sort_unstable(); ms.dedup();
    let mut ns: Vec<usize> = recs.iter().map(|r| r.n).collect(); ns.sort_unstable(); ns.dedup();
    let mut grid_actual = vec![vec![0f64; ns.len()]; ms.len()];
    let mut grid_gap_cap = vec![vec![0f64; ns.len()]; ms.len()];
    let mut grid_gap_rel = vec![vec![0f64; ns.len()]; ms.len()];
    let mut grid_gap_lb  = vec![vec![0f64; ns.len()]; ms.len()];
    for r in &recs { if let (Ok(i), Ok(j)) = (ms.binary_search(&r.m), ns.binary_search(&r.n)) {
        grid_actual[i][j] = r.actual as f64;
        grid_gap_cap[i][j] = (r.ub_cap - r.actual) as f64;
        grid_gap_rel[i][j] = (r.ub_rel - r.actual) as f64;
        grid_gap_lb[i][j]  = (r.actual - r.lb_band) as f64;
    }}
    let hm = |name:&str, data:&Vec<Vec<f64>>| -> Plot {
        let trace = HeatMap::new(ns.clone(), ms.clone(), data.clone());
        let mut plot = Plot::new(); plot.add_trace(trace);
        let layout = Layout::new()
            .title(name)
            .x_axis(Axis::new().title("n"))
            .y_axis(Axis::new().title("m"));
        plot.set_layout(layout);
        plot
    };
    for (name, data) in [
        ("actual", &grid_actual),
        ("gap_cap", &grid_gap_cap),
        ("gap_rel", &grid_gap_rel),
        ("gap_lb_band", &grid_gap_lb)
    ] { hm(name, data).write_html(out_dir.join(format!("heat_{name}.html"))); }
    // Line plots per m
    for &m in &ms { let mut plot = Plot::new(); let mut xs = Vec::new(); let mut ya=Vec::new(); let mut ylb=Vec::new(); let mut yub=Vec::new(); let mut yur=Vec::new();
        for &n in &ns { if let Some(r)=recs.iter().find(|r| r.m==m && r.n==n) { xs.push(n); ya.push(r.actual); ylb.push(r.lb_band); yub.push(r.ub_cap); yur.push(r.ub_rel); } }
        let add = |p:&mut Plot, y:&[i32], name:&str| { p.add_trace(Scatter::new(xs.clone(), y.iter().copied().collect::<Vec<_>>()).mode(Mode::LinesMarkers).name(name)); };
        add(&mut plot,&ya,"actual"); add(&mut plot,&ylb,"LB_band"); add(&mut plot,&yub,"UB_cap"); add(&mut plot,&yur,"UB_rel");
    let layout = Layout::new().title(format!("m={m}"));
    plot.set_layout(layout);
        plot.write_html(out_dir.join(format!("lines_m_{m}.html")));
    }
    Ok(())
}
