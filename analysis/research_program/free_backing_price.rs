//! Price unrestricted length on d edge columns plus one entirely free backing column.
use std::collections::HashMap;
type State=(i32,u64);
fn root(p:&[usize;20],mut i:usize)->usize{while p[i]!=i{i=p[i]}i}
pub(crate) fn edges(w:usize,(old,part):State)->Vec<State>{
    next(w,(old,part),false)
}
pub(crate) fn next(w:usize,(old,part):State,wired:bool)->Vec<State>{
    layer(w,(old,part),wired,true,false)
}
pub(crate) fn layer(w:usize,(old,part):State,wired:bool,spoke:bool,mandatory:bool)->Vec<State>{
    let all=(1<<w)-1;let free=if old<0{all}else{all&!(old<<1|old>>1)};
    let mut v=free;let mut out=vec![];
    loop{
        let mut p=std::array::from_fn(|i|i);
        // A persistent root, stored in the last frontier nibble.
        if wired{assert!(2*w<20);p[2*w]=((part>>(4*w))&15) as usize;if p[2*w]==w{p[2*w]=2*w}}
        for i in 0..w{p[i]=((part>>(4*i))&15)as usize}
        let mut ok=true;
        for i in 0..w{let j=w+i;
            for (present,k) in [(old>=0&&(old|v)>>i&1!=0,i),(i>0&&v>>(i.saturating_sub(1))&3!=0,j-1)]{
                if present{let a=root(&p,k);let b=root(&p,j);if a==b{ok=false;break}p[a]=b}
            }
            if !ok{break}
        }
        if ok{let mut first=[31;20];let mut q=0;
            if wired && (mandatory||spoke&&v&1!=0){let a=root(&p,w);let b=root(&p,2*w);if a==b{if v==0{break}v=(v-1)&free;continue}p[a]=b}
            for i in 0..w{let r=root(&p,w+i);if first[r]==31{first[r]=i}q|=(first[r] as u64)<<(4*i)}
            if wired{let r=root(&p,2*w);q|=(first[r].min(w) as u64)<<(4*w)}
            out.push((v,q))}
        if v==0{break}v=(v-1)&free
    }out
}
fn main(){
    let d:usize=std::env::args().nth(1).unwrap().parse().unwrap();
    let aq:i32=std::env::args().nth(2).unwrap().parse().unwrap();
    let bq:i32=std::env::args().nth(3).unwrap().parse().unwrap();
    assert!(d==3||d==6||d==9);
    let w=d+1;let init=(-1,(0..w).map(|i|(i as u64)<<(4*i)).sum());let mut states=vec![init];
    let mut ix=HashMap::from([(init,0)]);let mut arcs=vec![];let mut u=0;
    let ideal=(0..d).step_by(3).map(|i|1<<i).sum::<i32>();
    while u<states.len(){
        for t in edges(w,states[u]){let n=states.len();let j=*ix.entry(t).or_insert(n);
            if j==n{states.push(t)}
            let m=t.0&((1<<d)-1);
            let val=30*(m.count_ones() as i32-d as i32/3)+aq*i32::from(m!=ideal)-bq*i32::from(t.0>>d&1==0);
            arcs.push((u,j,val));
        }
        u+=1;
    }
    // Difference inequalities for all paths; exact integer potential.
    let mut f=vec![i32::MIN;u];f[0]=0;
    for _ in 0..2*u{
        let mut improved=false;
        for &(i,j,v) in &arcs{if f[i]!=i32::MIN&&f[j]<f[i]+v{f[j]=f[i]+v;improved=true}}
        if !improved{
            assert!(arcs.iter().all(|&(i,j,v)|f[j]>=f[i]+v));
            println!("d={d} states {u} arcs {}: 30*(marks-dH/3)+{aq}*bad-{bq}*holes <= {}",arcs.len(),f.iter().max().unwrap());return
        }
        if f.iter().max().unwrap()>&2000{println!("no potential below cutoff");return}
    }panic!("no finite certificate");
}
