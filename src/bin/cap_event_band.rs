//! Minimal local run/isolate/bottom-hole bill in a cropped all-height cap.
//! One free halo column on each side. Cost in half-units; all top spokes
//! contact the same old tree. A lost component is ignored (a relaxation).
use std::collections::HashMap;
pub(crate) type Key=(u16,u16,u64);
fn rt(p:&[u8;32],mut x:usize)->usize{while p[x] as usize!=x{x=p[x] as usize}x}
pub(crate) fn options(w:usize,(old,pending,part):Key,core:u16,first:bool,phase:usize,force:Option<u16>)->Vec<(Key,u32)>{
    let all=(1<<w)-1;let no=(old<<1)|(old>>1);
    let rails=(0..w).filter(|&x|x%3==phase).map(|x|1<<x).sum::<u16>();
    let free=if first{rails}else{all&!no};let mut m=force.unwrap_or(free);let mut out=vec![];
    if m&!free!=0{return out}
    loop{
        let mut p=std::array::from_fn(|i|i as u8);for i in 0..=w{p[i]=((part>>(4*i))&15) as u8}
        let mut ok=true;
        for i in 0..w{
            let u=w+i+1;
            for v in [(if (m|old)&(1<<i)!=0{Some(i+1)}else{None}),
                      (if i>0 && (m>>(i-1))&3!=0{Some(u-1)}else{None})].into_iter().flatten(){
                let a=rt(&p,u);let b=rt(&p,v);if a==b{ok=false;break}p[a]=b as u8
            }
            if !ok{break}
        }
        if ok{
            let mut ids=[31usize;32];let mut pk=0;
            for i in 0..=w{let z=rt(&p,if i==0{0}else{w+i});if ids[z]==31{ids[z]=i}pk|=(ids[z] as u64)<<(4*i)}
            let fresh=m&!old&core;
            let bill=2*(pending&!m).count_ones()+
                if first{0}else{(fresh&!(m<<1)).count_ones()+(fresh&!(m>>1)).count_ones()};
            out.push(((m,core&!(m|(m<<1)|(m>>1)|old),pk),bill))
        }
        if m==0 || force.is_some(){break}m=(m-1)&free
    }
    out
}
#[allow(dead_code)]
fn main(){
    let args:Vec<usize>=std::env::args().skip(1).map(|s|s.parse().unwrap()).collect();
    let (w,phase,limit)=(args[0]+2,args[1],args[2] as u32);assert!(w<=14 && phase<3);
    let core=(1u16<<(w-1))-2;
    let mode=*args.get(3).unwrap_or(&0);
    let suffix:Vec<u16>=args.iter().skip(4).map(|&v|v as u16).collect();
    let emit=mode!=0;
    let mut table=vec![limit+1;1<<w];
    let rails=(0..w).filter(|&x|x%3==phase).map(|x|1<<x).sum::<u16>();
    let mut best=HashMap::new();let mut buckets=vec![vec![];(limit+1)as usize];
    for (u,_) in options(w,(rails,0,0),core,true,phase,None){best.insert(u,0u32);buckets[0].push(u)}
    for cost in 0..=limit{
        while let Some(u)=buckets[cost as usize].pop(){
            if best[&u]!=cost{continue}
            let terminal=2*((core&!u.0).count_ones()+u.1.count_ones());
            // A null-height extension is legal only at an actual last row.
            // For a known essential bar, no vertex on the row can
            // already be connected to the wired upper boundary.
            let disjoint=(0..w).all(|i| u.2>>(4*(i+1))&15!=0);
            if mode==3{
                let mut cur=u;let mut d=cost;let mut ok=true;
                for &v in &suffix{
                    if let Some((nx,z))=options(w,cur,core,false,phase,Some(v)).into_iter().next(){
                        cur=nx;d+=z;
                    }else{ok=false;break}
                    if d>limit{ok=false;break}
                }
                if ok && (0..w).all(|i| cur.2>>(4*(i+1))&15!=0){
                    d+=2*((core&!cur.0).count_ones()+cur.1.count_ones());
                    table[u.0 as usize]=table[u.0 as usize].min(d);
                }
            }else if cost+terminal<=limit && (mode!=2 || disjoint){
                if !emit{println!("OPEN bill {} visited {}",cost+terminal,best.len());return}
                table[u.0 as usize]=table[u.0 as usize].min(cost+terminal);
            }
            for (v,z) in options(w,u,core,false,phase,None){
                let d=cost+z;if d>limit || best.get(&v).is_some_and(|&t|t<=d){continue}
                best.insert(v,d);buckets[d as usize].push(v)
            }
        }
    }
    if emit{for z in table{print!("{z} ")}println!()}else{println!("EMPTY bill <= {limit} visited {}",best.len())}
}
