//! Price nine old rows at a connected depth-nine path with freely positioned holes.
#[allow(dead_code)] #[path="free_backing_price.rs"] mod base;
use std::collections::HashMap;
fn main(){
    let args:Vec<i32>=std::env::args().skip(1).map(|s|s.parse().unwrap()).collect();
    let gap=args[0];assert!(gap>=2);
    let narrow=gap>=3;let w=if narrow{8}else{9};
    let ban=args.get(4).copied()==Some(1);
    let badprice=args.get(4).copied()==Some(2);
    let ban4=args.get(4).copied()==Some(3);assert!(!ban4||narrow);
    let init=((-1,(0..=w).map(|i|(i as u64)<<(4*i)).sum()),gap);
    let mut states=vec![init];let mut ix=HashMap::from([(init,0)]);let mut arcs=vec![];let mut i=0;
    while i<states.len(){
        let (s,age)=states[i];
        for backed in [true,false]{
            if !backed&&age<gap-1{continue}
            if !narrow&&backed&&s.0>=0&&s.0&1!=0{continue}
            let age2=if backed{(age+1).min(gap)}else{0};
            for t in base::layer(w,s,true,backed||!narrow,backed&&!narrow){
                if ban&&t.0==if narrow{146}else{292}{continue}
                if ban4&&[146,145,137,73].contains(&t.0){continue}
                if !narrow&&s.0>=0&&age>0&&t.0&1!=0{continue}
                let k=(t,age2);let n=states.len();let j=*ix.entry(k).or_insert(n);
                if j==n{states.push(k)}
                let paid=if badprice{t.0!=if narrow{146}else{292}}else{!backed&&t.0&1!=0};
                let premium=if paid{args[2]}else{0};
                arcs.push((i,j,args[1]*t.0.count_ones() as i32+premium));
            }
        }
        i+=1;
    }
    let protect=args.get(3).copied().unwrap_or(0);
    let pitch=if narrow{(1<<7)|(1<<4)|(1<<1)}else{(1<<8)|(1<<5)|(1<<2)};
    let mut d=vec![-999999;i];d[0]=0;let mut seen=HashMap::new();let mut peak=0;
    for h in 1..180{
        let mut e=vec![-999999;i];
        for &(a,b,v) in &arcs{if d[a]>-999999&&(h>protect||states[b].0.0==pitch){e[b]=e[b].max(d[a]+v)}}
        let z=*e.iter().max().unwrap();
        let close=if protect>0{e.iter().enumerate().filter(|(j,_)|states[*j].0.0==pitch).map(|(_,v)|*v).max().unwrap()}else{z};
        peak=peak.max(close-3*h*args[1]);
        let sig:Vec<_>=e.iter().map(|&v|if v==-999999{v}else{v-z}).collect();
        if let Some((old,c))=seen.insert(sig,(h,z)){
            assert!(old>=protect);
            let drift=z-c-3*(h-old)*args[1];
            if gap==3&&args[1..]==[1,0]{assert!(drift==0&&peak==5);}
            if gap==4&&badprice&&args[1]==9&&args[2]==1{assert!(drift==0&&peak==46);}
            println!("gap {gap} scale {} premium {} (nonpitch={badprice}): repeat {old}..{h}, increment {}, excess over 3L {drift}, peak {peak}",args[1],args[2],z-c);return;
        }d=e;
    }panic!("no recurrence");
}
