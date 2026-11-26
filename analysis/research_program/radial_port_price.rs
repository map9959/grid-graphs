//! A two-rim rank potential for a *chain* of consecutive three-layer crops.
use std::collections::HashMap;
const W:usize=4;
type S=(u8,u16,u8,u8);
fn root(q:&[usize;8],mut i:usize)->usize{while q[i]!=i{i=q[i]}i}
fn go((old,part,flags,older):S,m:u8,q:i32,a:i32,l:i32,all:bool,gc:i32)->Option<(S,i32)>{
    if old!=16&&(old<<1|old>>1)&m!=0{return None}
    let mut par=std::array::from_fn(|i|if i<4{((part>>(4*i))&15)as usize}else{i});
    let mut f=[false;8];for i in 0..4{f[i]=flags>>i&1!=0;f[4+i]=(i==0||i==3)&&(all||m>>i&1!=0);}
    let b=if all{2}else{(m&9).count_ones()as i32};
    let t=if all{(!(m|old)&9).count_ones()as i32}else{(m&!(old|older)&9).count_ones()as i32};
    let mut score=q*((m&7).count_ones()as i32-1)+a*((m>>3)as i32-(m&1)as i32)+l*(2*b-t);
    let gaps=!(m|old);score+=gc*((gaps>>3&1)as i32-(gaps&1)as i32);
    for i in 0..W{
        for (v,ok) in [(i,old!=16&&(old|m)>>i&1!=0),(4+i-1,i!=0&&m>>(i.saturating_sub(1))&3!=0)]{
            if !ok{continue}let z=root(&par,4+i);let w=root(&par,v);if z==w{return None}
            if f[z]&&f[w]{score-=2*l}f[z]|=f[w];par[w]=z;
        }
    }
    let mut ids=[9;8];let mut part=0;let mut bits=0;
    for i in 0..W{let r=root(&par,4+i);ids[r]=ids[r].min(i);part|=(ids[r]as u16)<<(4*i);bits|=(f[r]as u8)<<i}
    Some(((m,part,bits,old&9),score))
}
fn main(){let a:Vec<i32>=std::env::args().skip(1).map(|s|s.parse().unwrap()).collect();
    let init=(16,0x3210,0,9);let mut st=vec![init];let mut ix=HashMap::from([(init,0)]);let mut arcs=vec![];let mut i=0;
    while i<st.len(){for m in 0..16{if let Some((s,v))=go(st[i],m,a[0],a[1],a[2],a.get(3)==Some(&1),a.get(4).copied().unwrap_or(0)){
        let n=st.len();let j=*ix.entry(s).or_insert(n);if j==n{st.push(s)}arcs.push((i,j,v))
    }}i+=1}
    let mut d=vec![i32::MIN;i];d[0]=0;
    for _ in 0..i{let mut change=false;for &(i,j,v) in &arcs{if d[i]!=i32::MIN&&d[j]<d[i]+v{d[j]=d[i]+v;change=true}}
        if !change{
            println!("finite: {} states {} arcs, peak {}",i,arcs.len(),d.iter().max().unwrap());
            if a.get(5)==Some(&1){let mut z=vec![vec![];i];
                for &(u,v,w) in &arcs{if d[u]+w==d[v]{z[u].push(v)}}
                let mut cycles=std::collections::BTreeSet::new();
                for start in 0..i{let mut q=vec![vec![start]];
                    while let Some(p)=q.pop(){for &v in &z[*p.last().unwrap()]{
                        if v==start{let mut word:Vec<_>=p.iter().map(|&j|st[j].0).collect();let mut best=word.clone();
                            for _ in 1..word.len(){word.rotate_left(1);best=best.min(word.clone())}cycles.insert(best);
                        }else if v>start&&!p.contains(&v){let mut t=p.clone();t.push(v);q.push(t)}
                    }}
                }println!("critical masks {cycles:?}");
                let mut reach=vec![vec![false;i];i];
                for j in 0..i{for &k in &z[j]{reach[j][k]=true}}
                for k in 0..i{for j in 0..i{if reach[j][k]{for v in 0..i{reach[j][v]|=reach[k][v]}}}}
                let mut done=vec![false;i];
                for j in 0..i{if !done[j]&&reach[j][j]{
                    let vs:Vec<_>=(0..i).filter(|&k|reach[j][k]&&reach[k][j]).collect();
                    let mut words=std::collections::BTreeSet::new();for &k in &vs{done[k]=true;words.insert(st[k].0);}
                    println!("component {} states; masks {words:?}",vs.len())
                }}
            }
            return
        }
    }println!("positive cycle")
}
