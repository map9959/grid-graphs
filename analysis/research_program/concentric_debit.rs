//! Four physical layers: test a telescoping hole charge between radii 0 and 3.
use std::collections::HashMap;
type Pt=(i32,i32);
fn root(q:&[usize;20],mut a:usize)->usize{while q[a]!=a{a=q[a]}a}
fn order(n:i32)->(Vec<Pt>,HashMap<usize,(usize,usize)>) {
    let w=4;let mut out=vec![];let mut ends=HashMap::new();
    for s in 0..4{
        let mut a=vec![];
        for (j,x) in (w..n/2).rev().enumerate(){for y in 0..w{a.push((y,x))}
            ends.insert(out.len()+a.len()-1,(2*s,j));}
        for t in (1-w..w).rev(){
            for y in 0..w{let x=y+t;if x>=0&&x<w{a.push((y,x))}}
            if t==0{a.push((w,w))}
        }
        for (j,y) in (w..n-n/2).enumerate(){for x in 0..w{a.push((y,x))}
            ends.insert(out.len()+a.len()-1,(2*s+1,j));}
        for (mut y,mut x) in a{for _ in 0..s{(y,x)=(n-1-x,y)}out.push((y,x))}
    }(out,ends)
}
fn solve(n:i32,scale:i32,alpha:i32,fees:[i32;2],modes:u32,rank:i32,gc:i32,angle:&[i32])->i32{
    let (o,ends)=order(n);let ix:HashMap<_,_>=o.iter().enumerate().map(|(j,&p)|(p,j)).collect();assert_eq!(ix.len(),o.len());
    let adj=|(y,x):Pt|[(y+1,x),(y-1,x),(y,x+1),(y,x-1)];
    let last:Vec<_>=o.iter().map(|&p|adj(p).iter().filter_map(|t|ix.get(t)).copied().max().unwrap()).collect();
    let dep=|(y,x):Pt|y.min(x).min(n-1-x).min(n-1-y);
    let corner=|(y,x):Pt|y.min(n-1-y)==x.min(n-1-x);
    assert!(angle.len()<=10);let center=(0..angle.len()).fold(0u64,|v,j|v+(16<<(6*j)));
    let mut live:Vec<usize>=vec![];let mut d=HashMap::from([(0u128,(0,center))]);let stride=if rank==0{5}else{6};
    let trace=std::env::var_os("CONCENTRIC_TRACE").is_some();assert!(!trace||o.len()<=384);
    let mut words=HashMap::new();if trace{words.insert(0u128,[0u64;6]);}
    let pump=std::env::var_os("CONCENTRIC_PUMP").is_some();
    let period=std::env::var("CONCENTRIC_PERIOD").ok().map(|v|v.parse::<usize>().unwrap()).unwrap_or(1);
    let mut hit=[None;8];let mut snaps=vec![HashMap::new();period];let mut ops=vec![];let mut prevops=vec![vec![];period];
    let rigid=std::env::var_os("CONCENTRIC_RIGID").is_some();
    let iso=std::env::var_os("CONCENTRIC_ISO").is_some();assert!(!iso||rigid);
    let mut same=0;
    for (i,&p) in o.iter().enumerate(){
        let l=live.len();assert!(l<12);
        let v=dep(p);let side=if p.0==v{0}else if p.1==v{1}else if p.0==n-1-v{2}else{3};
        let alt=modes>>side&1!=0;let straight=p.0.min(n-1-p.0)>=4||p.1.min(n-1-p.1)>=4;
        let dist=(p.0.min(n-1-p.0).max(p.1.min(n-1-p.1))-v)as usize;
        let sign=if v==0{1}else if v==3{-1}else{0};
        let w=match v{0=>scale-alpha,1|2=>scale,3=>alpha,_=>0}+sign*angle.get(dist).unwrap_or(&0);
        let prev:Vec<_>=adj(p).iter().filter_map(|t|ix.get(t)).filter_map(|j|live.iter().position(|k|k==j)).map(|k|{
            let t=o[live[k]];let rim=(v==0||v==3)&&dep(t)==v;
            (k,if !alt&&rim&&!corner(t)&&!corner(p){fees[(v/3)as usize]}else{0},rim)}).collect();
        live.push(i);let keep:Vec<_>=(0..=l).filter(|&j|last[live[j]]>i).collect();
        let rail=p.1%3==0;
        let inner_optional=(p.0==3||p.0==n-4)&&p.1>3&&p.1<n-4&&rail;
        let outer_optional=(p.0==0||p.0==n-1)&&p.1>0&&p.1<n-1&&rail;
        if pump{ops.push((l,v,w,alt,straight,rigid&&rail,rigid&&inner_optional,rigid&&outer_optional,prev.clone(),keep.clone()));}
        let mut e=HashMap::new();
        let mut word=HashMap::new();
        for (&s,&(z,ftr)) in &d{for m in 0..=u128::from(v<=3){
            if rigid&&v==3&&(m!=u128::from(rail)&&!inner_optional){continue}
            let bad=rigid&&v<=3&&m!=u128::from(rail)&&!outer_optional;
            let mut alone=if iso{s>>80&4095}else{0};
            if iso&&v==3&&!rail&&m==0{alone|=1<<l}
            let mut q=std::array::from_fn(|j|if j<l{((s>>(stride*j))&15)as usize}else{j});
            let mut flags=if rank==0{[false;20]}else{std::array::from_fn(|j|j<l&&s&(32<<(stride*j))!=0)};flags[l]=rank!=0&&(v==0||v==3);
            let mut ok=true;let mut bill=0;for &(j,fee,rim) in &prev{
                if m>0||s&(16<<(stride*j))!=0{let a=root(&q,j);let b=root(&q,l);
                    if a==b{ok=false;break}q[a]=b;flags[b]|=flags[a];flags[a]=false;alone&=!(1<<j|1<<l);
                }else if fee<0{ok=false;break}else{bill+=fee+if rim{rank+if v==0{gc}else{-gc}}else{0}}
            }
            if !ok{continue}let mut ids=[20;20];let mut key=0;
            if rigid{key=(s&(1<<110))|(u128::from(bad)<<110)}
            if alt&&straight&&v<4{
                let b=if v==0{m}else{s>>100};
                if v==3{bill+=i32::from(b!=m)}else{key=b<<100}
            }
            for (j,&u) in keep.iter().enumerate(){let r=root(&q,u);ids[r]=ids[r].min(j);
                key|=(ids[r]as u128|if u==l{16*m}else{s>>(stride*u)&16}|32*flags[r]as u128)<<(stride*j);
                if alone>>u&1!=0{key|=1<<(80+j);alone^=1<<u}}
            bill+=6*alone.count_ones()as i32;
            if rank!=0{for j in 0..=l{if flags[j]&&q[j]==j&&ids[j]==20{bill-=2*rank}}}
            let c=e.entry(key).or_insert((i32::MIN,0u64));let val=z+w*m as i32-bill;
            if val>c.0{let dx=if m==1&&dist<angle.len(){(sign as i64)<<(6*dist)}else{0};
                *c=(val,(ftr as i64+dx)as u64);if trace{let mut bits=words[&s];bits[i/64]|=(m as u64)<<(i%64);word.insert(key,bits);}}
        }}
        live=keep.iter().map(|&j|live[j]).collect();d=e;
        if trace{words=word}
        if pump{if let Some(&(side,j))=ends.get(&i){
            same=if j>=period&&ops==prevops[j%period]{same+1}else{0};
            let snap=&mut snaps[j%period];
            if pump&&std::env::var_os("CONCENTRIC_LOG").is_some()&&j%12==9{
                println!("side {side} step {j}, matching operators {same}, excess {:?}",d.iter().map(|(k,v)|snap.get(k).map(|u:&(i32,u64)|v.0-u.0-scale*period as i32).unwrap_or(99999)).max())
            }
            if same>=period&&hit[side].is_none()&&d.iter().all(|(k,v)|snap.get(k).is_some_and(|u:&(i32,u64)|v.0<=u.0+scale*period as i32)){
                hit[side]=Some(j)
            }
            snap.clone_from(&d);prevops[j%period]=std::mem::take(&mut ops)
        }}
    }
    if pump{println!("eight verified pump positions {hit:?}");assert!(hit.iter().all(Option::is_some))}
    if !angle.is_empty(){println!("angle {:?}",(0..angle.len()).map(|j|((d[&0].1>>(6*j))&63)as i32-16).collect::<Vec<_>>())}
    if trace{let bits=words[&if rigid{1<<110}else{0}];for y in 0..n{println!("{}",(0..n).map(|x|if rigid&&dep((y,x))>3&&x%3==0||ix.get(&(y,x)).is_some_and(|&i|bits[i/64]>>(i%64)&1!=0){'#'}else{'.'}).collect::<String>())}}
    if rigid{let good=d[&0].0+24*alpha;let bad=d[&(1<<110)].0+24*alpha;
        if iso&&(scale,alpha,rank,gc)==(12,4,3,-1)&&angle==[-3]&&fees==[0,0]{
            assert_eq!(good,48*n-60);assert!(bad<good)
        }
        println!("pure / defective completion {good} / {bad}");}
    d[&0].0+24*alpha
}
fn main(){let a:Vec<i32>=std::env::args().skip(1).map(|z|z.parse().unwrap()).collect();
    let fees=if a.len()>=6{[a[4],a[5]]}else{[-1,-1]};
    let arg=|i|a.get(i).copied().unwrap_or(0);
    for n in (a[0]..=a[1]).step_by(3){let z=solve(n,a[2],a[3],fees,arg(6)as u32,arg(7),arg(8),&a[9.min(a.len())..]);
        println!("side {n}: weighted three layers {z}, deficit from 4n = {}",4*n*a[2]-z)}
}
