//! Four-row transfer, pricing changes of the two end words jointly.
#[allow(dead_code)] #[path="free_backing_price.rs"] mod base;
use std::collections::HashMap;
fn main(){
    let a:Vec<i32>=std::env::args().skip(1).map(|s|s.parse().unwrap()).collect();
    let (scale,fee)=(a[0],a[1]);let init=(-1,0x3210u64);let mut st=vec![init];let mut ix=HashMap::from([(init,0)]);
    let mut arcs=vec![];let mut i=0;
    while i<st.len(){for t in base::edges(4,st[i]){
        let b=t.0&1;let c=t.0>>3;let mut cost=scale*(b+c+2*(t.0&6).count_ones()as i32-2);
        if b!=c{if fee<0{continue}cost-=fee}
        let n=st.len();let j=*ix.entry(t).or_insert(n);if j==n{st.push(t)}arcs.push((i,j,cost))
    }i+=1}
    let mut d=vec![i32::MIN;i];d[0]=0;
    for _ in 0..i{let mut change=false;
        for &(i,j,w) in &arcs{if d[i]!=i32::MIN&&d[i]+w>d[j]{d[j]=d[i]+w;change=true}}
        if !change{println!("{} states, {} inequalities; peak {}",st.len(),arcs.len(),d.iter().max().unwrap());return}
    }println!("positive cycle");
}
