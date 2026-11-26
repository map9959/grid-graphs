//! Periodic cap attached to one wired pitch-three row. A floating quotient
//! component may be unicyclic (it could lift to an infinite path). Winding
//! is not required, so this is a necessary condition, not a construction.
use std::collections::HashMap;
type Key=(u16,u64,u16);
fn root(p:&[usize;32],mut i:usize)->usize{while p[i]!=i{i=p[i]}i}
fn edge(p:&mut [usize;32],c:&mut [bool;32],i:usize,j:usize)->bool{
    let a=root(p,i);let b=root(p,j);
    if a==b{if c[a]{return false}c[a]=true;}else{
        if c[a]&&c[b]{return false}p[a]=b;c[b]|=c[a];
    }true
}
fn arcs(w:usize,(old,part,cycles):Key)->Vec<Key>{
    let mut out=vec![];let all=(1<<w)-1;
    let no=((old<<1)|(old>>(w-1))|(old>>1)|((old&1)<<(w-1)))&all;
    let free=all^no;let mut m=free;
    loop{
        let mut p=std::array::from_fn(|i|i);let mut c=[false;32];
        for i in 0..=w {p[i]=((part>>(4*i))&15) as usize;c[i]=cycles&(1<<i)!=0}
        let mut ok=true;
        for i in 0..w {
            let j=(i+1)%w;let u=w+1+i;
            if (old|m)&(1<<i)!=0{ok&=edge(&mut p,&mut c,i+1,u)}
            if m&((1<<i)|(1<<j))!=0{ok&=edge(&mut p,&mut c,u,w+1+j)}
            if !ok{break}
        }
        if ok{
            let mut ids=[31usize;32];let mut pk=0;let mut ck=0;
            for i in 0..=w {
                let u=root(&p,if i==0{0}else{w+i});if ids[u]==31{ids[u]=i}
                pk|=(ids[u] as u64)<<(4*i);if c[u]{ck|=1<<ids[u]}
            }
            out.push((m,pk,ck))
        }
        if m==0{break}m=(m-1)&free;
    }
    out
}
fn main(){
    let w:usize=std::env::args().nth(1).unwrap().parse().unwrap();
    assert!(w%3==0 && (3..=15).contains(&w));
    let rails=(0..w).step_by(3).map(|i|1<<i).sum();
    // A dummy cycle on the permanent root prohibits any actual cycle
    // in the component wired to that root.
    let mut dp=HashMap::from([((rails,0,1),0i32)]);
    let mut cache=HashMap::new();
    for h in 1..=160 {
        let mut nd=HashMap::new();
        for (&k,&v) in &dp{for &u in cache.entry(k).or_insert_with(||arcs(w,k)).iter(){
            let score=v+u.0.count_ones() as i32-(w/3) as i32;
            nd.entry(u).and_modify(|a:&mut i32|*a=(*a).max(score)).or_insert(score);
        }}
        let mx=*nd.values().max().unwrap();
        if h<12 || h%10==0{println!("h={h} bonus={mx} states={}",nd.len())}
        if nd.iter().all(|(u,&v)|dp.get(u).is_some_and(|&a|a>=v)){
            println!("full normalized vector dominated at {h}; subsequent bonuses <= {mx}");break
        }
        dp=nd;
    }
}
