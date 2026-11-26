//! Arbitrary ten-bit slices: price short distances between ninth-row holes.
#[allow(dead_code)] #[path="free_backing_price.rs"] mod base;
use std::collections::HashMap;
fn main(){
    let a:Vec<i32>=std::env::args().skip(1).map(|s|s.parse().unwrap()).collect();
    let (scale,c1,c2,c3,bonus)=(a[0],a[1],a[2],a[3],a[4]);assert!(scale>0);
    let init=((-1,(0..10).map(|i|(i as u64)<<(4*i)).sum()),3usize);
    let mut states=vec![init];let mut ix=HashMap::from([(init,0u32)]);let mut arcs=vec![];let mut row=vec![];
    let mut i=0;
    while i<states.len(){
        row.push(arcs.len());let (s,age)=states[i];
        for t in base::edges(10,s){
            let hole=t.0&512==0;let age2=if hole{0}else{(age+1).min(3)};
            let n=states.len();let j=*ix.entry((t,age2)).or_insert(n as u32);
            if j as usize==n{states.push((t,age2))}
            let m=t.0&511;
            let v=scale*(m.count_ones()as i32-3)+bonus*i32::from(m!=73)
                -if hole{[c1,c2,c3,0][age]}else{0};
            arcs.push((j,i16::try_from(v).unwrap()));
        }i+=1
    }
    row.push(arcs.len());let mut f=vec![i32::MIN;states.len()];f[0]=0;
    for _ in 0..200{
        let mut change=false;
        for i in 0..states.len(){let z=f[i];if z==i32::MIN{continue}
            for &(j,v) in &arcs[row[i]..row[i+1]]{let z=z+v as i32;let p=&mut f[j as usize];if *p<z{*p=z;change=true}}
        }
        if !change{
            assert!((0..states.len()).all(|i|arcs[row[i]..row[i+1]].iter().all(|&(j,v)|f[j as usize]>=f[i]+v as i32)));
            println!("weights {a:?}, {} states, {} inequalities, max excess {}",states.len(),arcs.len(),f.iter().max().unwrap());return
        }
        if f.iter().max().unwrap()>&(200*scale){break}
    }
    println!("no certificate with weights {a:?}");
}
