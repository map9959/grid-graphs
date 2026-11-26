//! Exact all-length price of the actual dependent donor spokes, not just occupied holes.
#[allow(dead_code)] #[path="free_backing_price.rs"] mod base;
use std::collections::HashMap;
const W:usize=8;
fn root(p:&[usize;17],mut v:usize)->usize{while v!=p[v]{v=p[v]}v}
fn wired(old:i32,q:u64,v:i32)->(u64,i32){
    let mut p=std::array::from_fn(|i|i);
    for j in 0..W{p[j]=((q>>(4*j))&15)as usize;}
    let z=((q>>(4*W))&15)as usize;if z<W{p[2*W]=z;}
    let mut extra=0;
    let mut edge=|a,b|{let a=root(&p,a);let b=root(&p,b);if a==b{extra+=1}else{p[a]=b}};
    for i in 0..W{
        if old>=0&&(old|v)>>i&1!=0{edge(i,W+i)}
        if i>0&&v>>(i-1)&3!=0{edge(W+i-1,W+i)}
    }
    if v&1!=0{edge(W,2*W)}
    let mut ids=[W;17];let mut res=0;
    for i in 0..W{let r=root(&p,W+i);ids[r]=ids[r].min(i);res|=(ids[r]as u64)<<(4*i);}
    (res|((ids[root(&p,2*W)]as u64)<<(4*W)),extra)
}
fn main(){
    let args:Vec<i32>=std::env::args().skip(1).map(|s|s.parse().unwrap()).collect();
    let(gap,scale,price)=(args[0],args[1],args[2]);assert!(gap>=3&&scale>0);
    let p0=(0..=W).map(|i|(i as u64)<<(4*i)).sum();
    let init=((-1,p0),p0,gap-1);let mut states=vec![init];let mut ix=HashMap::from([(init,0)]);
    let mut arcs=vec![];let mut u=0;let mut transitions=HashMap::new();let mut second=HashMap::new();
    while u<states.len(){
        let (s,q,age)=states[u];
        for backed in [false,true]{
            if !backed&&age<gap-1{continue}
            let prev=transitions.entry((s,backed)).or_insert_with(||base::layer(W,s,true,backed,false));
            for &t in prev.iter(){
                let(q2,b)=*second.entry((s.0,q,t.0)).or_insert_with(||wired(s.0,q,t.0));
                let k=(t,q2,if backed{(age+1).min(gap-1)}else{0});
                let n=states.len();let j=*ix.entry(k).or_insert(n);if n==j{states.push(k)}
                arcs.push((u as u32,j as u32,(scale*t.0.count_ones() as i32+price*b)as i16));
            }
        }
        u+=1;
    }
    drop(transitions);drop(second);
    let mut seen=HashMap::new();let mut d=vec![-999999;u];d[0]=0;let mut peak=0;
    for h in 1..200{
        let mut e=vec![-999999;u];for &(a,b,val) in &arcs{
            if d[a as usize]>=0{e[b as usize]=e[b as usize].max(d[a as usize]+val as i32);}
        }
        let z=*e.iter().max().unwrap();peak=peak.max(z-3*h*scale);
        let sig:Vec<_>=e.iter().map(|&v|if v<0{v}else{v-z}).collect();
        if let Some((l,s))=seen.insert(sig,(h,z)){
            println!("gap {gap} {u} states {} arcs; {scale}*marks+{price}*nullity: prefix {l}..{h}, shift {}, drift {}, max excess {peak}",
                     arcs.len(),z-s,z-s-3*(h-l)*scale);return
        }
        d=e;
    }panic!("no recurrence");
}
