//! Exact vertex frontier for a hole with private roots and five port pairs.
//! Input: vertex count followed by one list of earlier neighbors per vertex;
//! a positive 1-based neighbor denotes OR of the two marks, negative AND.
use std::collections::HashMap;
use std::io::{self,Read};
fn root(p:&[u8;24],mut i:usize)->usize {
    while p[i] as usize!=i {i=p[i] as usize} i
}
fn main(){
    let mut text=String::new();io::stdin().read_to_string(&mut text).unwrap();
    let clip=std::env::args().any(|v|v=="--classes");
    let distribution=clip || std::env::args().any(|v|v=="--counts");
    let near=std::env::args().any(|v|v=="--near");assert!(!near||!distribution);
    let packed=std::env::args().any(|v|v=="--packed");assert!(!packed||!distribution&&!near);
    let weights:Vec<u32>=std::env::args().skip(1).filter(|v|!v.starts_with("--")).map(|v|v.parse().unwrap()).collect();
    let mark_price=weights.first().copied().unwrap_or(1);let rank_price=weights.get(1).copied().unwrap_or(1);
    let mut a=text.split_whitespace().map(|v|v.parse::<i32>().unwrap());
    let n=a.next().unwrap() as usize;
    let mut last:Vec<_>=(0..n).collect();let mut prev=Vec::new();
    for i in 0..n {
        let len=a.next().unwrap();let mut es=Vec::new();
        for _ in 0..len {let v=a.next().unwrap();let j=(v.unsigned_abs() as usize-1)%n;
            assert!(j<i);es.push((j,if v<0 {2} else if v as usize>n {3} else {1}));last[j]=i;}
        prev.push(es);
    }
    let fixed:Vec<_>=(0..n).map(|_|a.next().unwrap_or(-1)).collect();
    let mut dp=HashMap::from([(0u128,0u32)]);let mut live:Vec<usize>=Vec::new();
    let mut spectra=HashMap::new();if near||packed{spectra.insert(0u128,[1u64,0,0]);}
    let rest:Vec<_>=a.collect();
    let tags=if rest.first()==Some(&-2){&rest[1..=n]}else{&[]};
    let stride=if tags.is_empty(){6}else{8};
    let rem=&rest[if tags.is_empty(){0}else{n+1}..];
    let stop=rem.iter().position(|&x|x == -3).unwrap_or(rem.len());
    let checkpoints:Vec<_>=rem[..stop].iter().map(|v|*v as usize).collect();
    let mut bans=HashMap::new();
    if stop<rem.len(){assert_eq!((rem.len()-stop-1)%3,0);for s in rem[stop+1..].chunks(3){
        bans.insert(s[0] as usize,(s[1]as u32,s[2]as u32));}}
    let mut snapshot=None;
    let mut psnap:Option<HashMap<u128,[u64;3]>>=None;
    let (mut peak,mut width)=(0,0);
    for i in 0..n {
        let l=live.len();assert!(l*stride<=if distribution{112}else{126});
        let es:Vec<_>=prev[i].iter().map(|&(j,mode)|(live.iter().position(|v|*v==j).unwrap(),mode)).collect();
        live.push(i);
        let keep:Vec<_>=(0..=l).filter(|&j|last[live[j]]>i).collect();
        let mut nd=HashMap::<u128,u32>::new();
        let mut sp=HashMap::<u128,[u64;3]>::new();
        for (s,z) in dp.drain(){
            let spec=if near||packed{spectra[&s]}else{[0;3]};
            let mut old=[0u8;24];let mut flags=0u32;
            for j in 0..l {let t=(s>>(stride*j)) as u8;old[j]=(t>>1)&31;flags|=((t&1) as u32)<<j;}
            old[l]=l as u8;
            'choice:for m in 0..=1u32 {
                if fixed[i]>=0 && fixed[i] as u32!=m {continue}
                let mut p=old;
                for &(j,mode) in &es {
                    let marked=(flags>>j)&1;
                    if (match mode {2=>m&marked,3=>1,_=>m|marked})==0 {continue}
                    let u=root(&p,l);let v=root(&p,j);if u==v{continue 'choice}
                    p[u]=v as u8;
                }
                let f=flags|(m<<l);let mut enc=0u128;let mut canon=[255u8;24];let mut tag=[0u8;24];let mut bonus=0;
                if !tags.is_empty(){
                    tag[root(&p,l)]=tags[i] as u8;
                    for j in 0..l{tag[root(&p,j)]|=((s>>(stride*j+6))&3) as u8;}
                }
                for (h,&j) in keep.iter().enumerate(){let r=root(&p,j);
                    if canon[r]==255{canon[r]=h as u8}
                    enc|=((2*canon[r] as u128)+((f>>j)&1) as u128+(u128::from(tag[r])<<6))<<(stride*h);
                }
                if !tags.is_empty(){for j in 0..=l{if tag[j]==1 && canon[j]==255{bonus+=1}}}
                if distribution{let ct=(s>>112)+u128::from(bonus);enc|=(if clip{ct.min(2)}else{ct})<<112}
                let v=nd.entry(enc).or_default();let nz=z+mark_price*m+if distribution&&!clip{0}else{rank_price*bonus};
                if near&&nz+2>=*v{
                    let dd=sp.entry(enc).or_insert([0;3]);
                    if nz>*v{let d=(nz-*v)as usize;
                        *dd=std::array::from_fn(|i|if i>=d{dd[i-d]}else{0});}
                    let off=v.saturating_sub(nz)as usize;
                    for j in off..3{assert!(bonus==0||spec[j-off]>>(64-bonus)==0);dd[j]|=spec[j-off]<<bonus;}
                }
                if packed{
                    let dd=sp.entry(enc).or_insert([0;3]);
                    for j in 0..3{if spec[j]!=0{
                        let k=(j+bonus as usize).min(2);
                        dd[k]=dd[k].max(spec[j]+(nz-z)as u64);
                    }}
                }
                *v=(*v).max(nz);
            }
        }
        live=keep.iter().map(|&j|live[j]).collect();dp=nd;
        if near||packed{spectra=sp}
        if let Some(&(msk,want))=bans.get(&i){
            let encode=|m:u32|(0..live.len()).fold(0u128,|v,j|v|(((m>>j&1)as u128)<<(stride*j)));
            assert!(msk>>live.len()==0);let m=encode(msk);let w=encode(want);
            dp.retain(|k,_|*k&m!=w);
            if near||packed{spectra.retain(|k,_|*k&m!=w)}
        }
        if checkpoints.contains(&i) {
            let mx=*dp.values().max().unwrap();
            if clip && std::env::args().any(|v|v=="--prefix") {
                let mut stop=[0;3];
                for (&s,&v) in &dp{
                    let mut count=0;
                    for j in 0..live.len(){
                        let t=(s>>(stride*j)) as u8;
                        if ((t>>1)&31) as usize==j && t>>6==1{count+=1}
                    }
                    let c=((s>>112) as usize+count as usize).min(2);
                    stop[c]=stop[c].max(v+rank_price*count);
                }
                eprintln!("prefix {i} {} {}",stop[1],stop[2]);
            }
            if let Some((ref old,z))=snapshot {
                let old:&HashMap<u128,u32>=old;
                let same=dp.len()==old.len()&&dp.iter().all(|(s,v)|old.get(s).is_some_and(|w|mx-v==z-w));
                let dominated=dp.iter().all(|(s,v)|old.get(s).is_some_and(|w|mx-v>=z-w));
                eprintln!("checkpoint {} same {} dominated {} shift {}",i,same,dominated,mx-z);
                if let Some(ref old)=psnap{
                    let eq=same&&spectra.iter().all(|(k,v)|v.iter().zip(old[k]).all(|(&a,b)|if a==0||b==0{a==b}else{a==b+(mx-z)as u64}));
                    eprintln!("packed checkpoint {i} same {eq} shift {}",mx-z);
                }
            }
            snapshot=Some((dp.clone(),mx));
            if packed{psnap=Some(spectra.clone())}
        }
        peak=peak.max(dp.len());width=width.max(live.len());
        if peak>2_000_000 {eprintln!("state cap at vertex {i}, width {}, states {peak}",live.len());std::process::exit(2)}
    }
    if packed{for (i,&v) in spectra[&0].iter().enumerate(){if v!=0{println!("{i} {}",v-1)}}}
    else if distribution{
        let mut vals:Vec<_>=dp.into_iter().map(|(s,v)|(s>>112,v)).collect();vals.sort();
        for (c,v) in vals{println!("{} {}",c,v)}
    }else{println!("{} {} {}",dp[&0],width,peak);
        if near{eprintln!("near-optimal class masks {:?}",spectra[&0]);}}
}
