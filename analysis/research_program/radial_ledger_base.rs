//! Exact boundary functional at the base of the three-layer induction.
use std::collections::HashMap;
fn root(q:&[usize;16],mut i:usize)->usize{while q[i]!=i{i=q[i]}i}
fn main(){
    let n=std::env::args().nth(1).unwrap().parse::<usize>().unwrap();assert!((2..=10).contains(&n));
    let mut d=HashMap::from([(0u128,(0,1u64))]);let mut live=vec![];
    for i in 0..n*n{let (y,x)=(i/n,i%n);let corner=(y==0||y+1==n)&&(x==0||x+1==n);
        let rim=y==0||y+1==n||x==0||x+1==n;let l=live.len();
        let mut prev=vec![];
        if y>0{prev.push((live.iter().position(|&j|j==i-n).unwrap(),x==0||x+1==n))}
        if x>0{prev.push((live.iter().position(|&j|j==i-1).unwrap(),y==0||y+1==n))}
        live.push(i);let keep:Vec<_>=(0..=l).filter(|&v|{let j=live[v];j+n<n*n&&j+n>i||j%n+1<n&&j+1>i}).collect();
        let mut e=HashMap::new();
        for (&s,&(z,count)) in &d{for m in 0..2u128{
            let mut q=std::array::from_fn(|j|if j<l{((s>>(6*j))&15)as usize}else{j});
            let mut f:[bool;16]=std::array::from_fn(|j|j<l&&s&(32<<(6*j))!=0);f[l]=rim;
            let mut cost=z+(12-4*i32::from(rim)-3*i32::from(corner))*m as i32;let mut ok=true;
            for &(j,r) in &prev{if m>0||s&(16<<(6*j))!=0{let a=root(&q,j);let b=root(&q,l);
                if a==b{ok=false;break}q[a]=b;f[b]|=f[a];f[a]=false
            }else if r{cost-=2}}
            if !ok{continue}
            let mut ids=[16;16];let mut k=0u128;
            for (j,&v) in keep.iter().enumerate(){let r=root(&q,v);ids[r]=ids[r].min(j);
                k|=(ids[r]as u128|32*f[r]as u128|if v==l{16*m}else{s>>(6*v)&16})<<(6*j)}
            for j in 0..=l{if f[j]&&q[j]==j&&ids[j]==16{cost+=6}}
            let p=e.entry(k).or_insert((i32::MIN,0u64));
            if cost>p.0{*p=(cost,count)}else if cost==p.0{p.1=p.1.saturating_add(count)}
        }}
        live=keep.iter().map(|&j|live[j]).collect();d=e
    }
    let (v,count)=d[&0];let z=v+16*(n as i32-1);println!("base {n} functional {z}, excess {}, equality count {count}",z-(4*n*n+14*n)as i32)
}
