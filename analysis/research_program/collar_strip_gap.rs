//! Straight-side mark capacity and crop-cost comparison.
#[allow(dead_code)]
#[path="free_backing_price.rs"] mod base;
use std::collections::HashMap;
fn main(){
    let w:usize=std::env::args().nth(1).unwrap().parse().unwrap();
    let mode=std::env::args().nth(2).unwrap_or_default();let ban=mode=="ban";let wired=mode=="wired";let pitch=(0..w).step_by(3).fold(0,|v,i|v|1<<i);
    assert!((1..=10).contains(&w)&&(!wired||w<10)&&matches!(mode.as_str(),""|"ban"|"wired"));
    let init=(-1,(0..w+wired as usize).map(|i|(i as u64)<<(4*i)).sum());let mut states=vec![init];
    let mut ix=HashMap::from([(init,0)]);let mut a=vec![];
    let mut u=0;
    while u<states.len(){
        for t in base::next(w,states[u],wired){
            if ban&&t.0==pitch{continue}
            let n=states.len();let j=*ix.entry(t).or_insert(n);if j==n{states.push(t)}
            a.push((u,j,t.0.count_ones() as i32));
        }
        u+=1;
    }
    let mut d=vec![-1000000;u];d[0]=0;
    let mut seen=HashMap::new();
    let mut maxima=vec![0];
    for h in 1..200{
        let mut e=vec![-1000000;u];for &(i,j,k) in &a{if d[i]>=0{e[j]=e[j].max(d[i]+k)}}
        let best=*e.iter().max().unwrap();let sig:Vec<_>=e.iter().map(|&v|if v<0{v}else{v-best}).collect();
        maxima.push(best);
        if let Some((old,z))=seen.insert(sig,(h,best)){
            let p=h-old;let inc=best-z;
            println!("w={w} states={u} arcs={} repeat {old}..{h} max {z}..{best} rate {inc}/{p}",a.len());
            if w==10&&!ban{assert!(old<=13&&p==1&&inc==4);}
            if w==9&&!ban&&!wired{assert!(old<=16&&p==4&&inc==14);}
            if w==8&&!wired{
                assert!(p==7&&inc==22);
                let c=maxima.iter().enumerate().map(|(i,v)|7*v-22*i as i32).max().unwrap();
                assert_eq!(c,34);
                println!("all lengths: 7M <= 22L + {c}");
            }
            if w==3&&wired{assert_eq!(inc, p as i32);}
            if w==10&&ban{
                let gap=(83..83+p).map(|l|4*l as i32-maxima[old+(l-old)%p]-((l-old)/p)as i32*inc).min().unwrap();
                assert!(inc<=4*p as i32&&gap>=12);println!("all straight lengths >=83 without a pitch slice: loss >= {gap} from 4L");
            }
            return;
        }d=e;
    }
    panic!("no verified vector recurrence");
}
