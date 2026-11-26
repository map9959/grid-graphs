//! Three-slice tariff for ten collar layers and one free core bit.
use std::collections::HashMap;
const W:usize=11;
const MASK:usize=(1<<W)-1;
const OLD:usize=(1<<(W-1))-1;
fn valid(u:usize,v:usize)->bool{
    let both=u&v;
    (u<<1|u>>1)&v==0 && both&(both>>2)==0
}
fn main(){
    let args:Vec<i32>=std::env::args().skip(1).map(|s|s.parse().unwrap()).collect();
    let (a,b)=(args[0],args[1]);let discount=args[2];
    let mut step=vec![vec![];MASK+1];
    for v in 0..=MASK{for u in 0..=MASK{if valid(u,v){step[v].push(u)}}}
    let mut ix=HashMap::new();let mut st=vec![];
    for v in 0..=MASK{for &u in &step[v]{ix.insert((u,v),st.len());st.push((u,v));}}
    let mut arcs=vec![];let mut starts=vec![];
    for &(u,v) in &st{
        starts.push(arcs.len());
        let m=v&OLD;
        let runs=m.count_ones() as i32-(m&(m>>1)).count_ones() as i32-(m&u).count_ones() as i32;
        let port=(v>>9&3==3) as i32;
        let base=2*((m&1==0)as i32+runs)-discount*port;
        let bad=(m!=585)as i32; // bits 0,3,6,9
        for &z in &step[v]{
            // If a mark at the middle column creates both length-two
            // spokes across a blank, take the transposed 2x3 cycle too.
            let eq=u&z; if eq&(eq>>1)!=0{continue}
            let isolates=(!(u|v|v<<1|v>>1|z)&OLD).count_ones() as i32;
            arcs.push((ix[&(v,z)] as u32,(a*bad-b*(base+2*isolates)) as i16));
        }
    }
    starts.push(arcs.len());
    // Max-plus difference inequalities on all paths; starting every state
    // at zero permits arbitrary end words. Stop on positive drift.
    let mut f=vec![0i32;st.len()];
    for _ in 0..100{
        let mut change=false;
        for i in 0..st.len(){
            let val=f[i];
            for &(j,w) in &arcs[starts[i]..starts[i+1]]{let j=j as usize;
                if f[j]<val+w as i32{f[j]=val+w as i32;change=true;}
            }
        }
        if !change{
            assert!((0..st.len()).all(|i|arcs[starts[i]..starts[i+1]].iter().all(|&(j,w)|f[j as usize]>=f[i]+w as i32)));
            if (a,b,discount)==(2,3,0){assert_eq!(*f.iter().max().unwrap(),4);}
            println!("{} tariff states {} verified inequalities; {a}*bad - {b}*double_debit <= {}",st.len(),arcs.len(),f.iter().max().unwrap());return
        }
        if *f.iter().max().unwrap()>1000{break}
    }
    println!("no certificate at {a}/{b}");
}
