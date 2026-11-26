//! Maximum mean mark count for an inserted strip with a full first row.
//! Frontier 0 (the bar) and 1 (always blank) can be replaced by one root.
use std::collections::HashMap;
type K=(u32,u64);
fn rt(p:&[u8;32],mut i:usize)->usize{while p[i] as usize!=i{i=p[i] as usize}i}
fn edges(w:usize,(old,part):K)->Vec<(K,i32)>{
    let free=((1<<w)-1)&!((old<<1)|(old>>1));
    let mut mask=free;let mut out=vec![];
    loop{
        let mut p=std::array::from_fn(|i|i as u8);
        for i in 0..=w{p[i]=((part>>(4*i))&15) as u8;}
        let mut ok=true;
        for i in 0..w{let j=w+1+i;
            for (exists,k) in [(((old|mask)>>i)&1!=0,i+1),(i>0&&(mask>>(i.saturating_sub(1)))&3!=0,j-1),(i==0&&mask&1!=0,0)]{
                if !exists{continue}let a=rt(&p,j);let b=rt(&p,k);
                if a==b{ok=false;break}p[a]=b as u8;
            }
            if !ok{break}
        }
        if ok{let mut ids=[31usize;32];let mut z=0;
            for i in 0..=w{let a=rt(&p,if i==0{0}else{w+i});if ids[a]==31{ids[a]=i}z|=(ids[a] as u64)<<(4*i)}
            out.push(((mask,z),mask.count_ones() as i32));
        }
        if mask==0{break}mask=(mask-1)&free;
    }out
}
fn main(){
    let h:usize=std::env::args().nth(1).unwrap().parse().unwrap();let w=h-1;assert!(w<=14);
    let ini=(0,(0..=w).map(|i|(i as u64)<<(4*i)).sum());let mut ix=HashMap::from([(ini,0)]);
    let mut states=vec![ini];let mut graph=vec![];let mut u=0;
    while u<states.len(){let mut row=vec![];
        for (s,c) in edges(w,states[u]){let n=states.len();let j=*ix.entry(s).or_insert(n);if j==n{states.push(s)}row.push((j,c))}
        graph.push(row);u+=1;
    }
    let mut dp=vec![-100000;u];dp[0]=0;let mut seen=HashMap::new();
    for n in 1..=220{let mut next=vec![-100000;u];for (i,row) in graph.iter().enumerate(){
        for &(j,c) in row{next[j]=next[j].max(dp[i]+c)}
    }
    let m=*next.iter().max().unwrap();let sig=next.iter().map(|v|(v-m).max(-30000) as i16).collect::<Vec<_>>();
    // Don't use the clipped signature until every state has finite cost.
    if next.iter().all(|&v|v>m-30000){if let Some((k,b))=seen.insert(sig,(n,m)){println!("depth {h} states {u} period {} gain {} from {k}",n-k,m-b);return}}
    dp=next;
    }panic!("no repeat");
}
