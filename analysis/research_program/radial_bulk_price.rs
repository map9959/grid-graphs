//! Test a proposed core flux on a strip of arbitrary fixed multiple-of-three depth.
use std::collections::HashMap;
type S=(i32,u64,u16);
fn rt(p:&[usize;20],mut i:usize)->usize{while p[i]!=i{i=p[i]}i}
fn main(){
    let a:Vec<i32>=std::env::args().skip(1).map(|s|s.parse().unwrap()).collect();
    let (d,q,al,l,gc)=(a[0]as usize,a[1],a[2],a[3],a[4]);assert!(d%3==0&&d>0&&d<=9);
    let w=d+1;let back=1<<d;let all=2*back-1;let init:S=(-1,(0..w).map(|j|(j as u64)<<(4*j)).sum(),0);
    let mut st=vec![init];let mut ix=HashMap::from([(init,0u32)]);let mut arcs=vec![];let mut starts=vec![];let mut i=0;
    while i<st.len(){starts.push(arcs.len());let(old,part,flags)=st[i];let free=if old<0{all}else{all&!(old<<1|old>>1)};
        let mut m=free;loop{
            let mut p=std::array::from_fn(|j|if j<w{(part>>(4*j)&15)as usize}else{j});
            let mut f:[bool;20]=std::array::from_fn(|j|j<w&&flags>>j&1!=0);f[w]=true;f[2*w-1]=true;
            let high=i32::from(old>=0&&(old|m)&1==0);let low=i32::from(old>=0&&(old|m)&back==0);
            let mut v=q*((m&(back-1)).count_ones()as i32-d as i32/3)+al*((m>>d)-(m&1))+gc*(low-high)+l*(4-high-low);
            let mut ok=true;for j in 0..w{
                for (u,edge) in [(j,old>=0&&(old|m)>>j&1!=0),(w+j-1,j>0&&m>>(j.saturating_sub(1))&3!=0)]{
                    if !edge{continue}let b=rt(&p,w+j);let c=rt(&p,u);if b==c{ok=false;break}
                    v-=2*l*i32::from(f[b]&&f[c]);f[b]|=f[c];p[c]=b
                }if !ok{break}
            }
            if ok{let mut ids=[30;20];let mut key=0;let mut ff=0;
                for j in 0..w{let r=rt(&p,w+j);ids[r]=ids[r].min(j);key|=(ids[r]as u64)<<(4*j);ff|=(f[r]as u16)<<j}
                let s=(m,key,ff);let n=st.len();let k=*ix.entry(s).or_insert(n as u32);
                if k as usize==n{st.push(s)}arcs.push((k,v as i16));
            }
            if m==0{break}m=(m-1)&free
        }i+=1
    }
    starts.push(arcs.len());let mut f=vec![0;i];
    for _ in 0..i.min(150){let mut change=false;
        for j in 0..i{let z=f[j];for &(k,v) in &arcs[starts[j]..starts[j+1]]{let u=&mut f[k as usize];
            if *u<z+v as i32{*u=z+v as i32;change=true}}}
        if !change{println!("finite: {i} states, {} arcs, peak {}",arcs.len(),f.iter().max().unwrap());return}
        if f.iter().max().unwrap()>&(100*q){break}
    }println!("no certificate")
}
