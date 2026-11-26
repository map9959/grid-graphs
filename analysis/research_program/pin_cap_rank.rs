//! All-depth rank prices for a cap above k consecutive pitch triples.
use std::collections::HashMap;
type State=(u16,u16,u64);
fn rt(p:&[u8;32],mut i:usize)->usize{while i!=p[i] as usize{i=p[i] as usize}i}
fn join(p:&mut[u8;32],i:usize,j:usize)->bool{let a=rt(p,i);let b=rt(p,j);p[a]=b as u8;a!=b}
fn main(){
    let k:usize=std::env::args().nth(1).unwrap().parse().unwrap();assert!((2..=4).contains(&k));
    let w=3*k;let mask=(1u16<<w)-1;let pitch=(0..k).map(|i|2<<(3*i)).sum();
    let ini=(pitch,0,(0..k+w).map(|i|((if i<k{i}else{(i-k)/3})as u64)<<(4*i)).sum());
    let limit=k-2;let mut bins=vec![Vec::new();limit+1];let mut best:HashMap<State,usize>=HashMap::new();
    let mut price=vec![limit+1;k+1];
    bins[0].push((ini,true));
    for cost in 0..=limit{
        while let Some(((old,waiting,part),first))=bins[cost].pop(){
            if !first{
                if best[&(old,waiting,part)]!=cost{continue}
                let classes=(0..k).filter(|&i| (part>>(4*i))&15==i as u64).count();
                let end=cost+(mask^old).count_ones() as usize+waiting.count_ones() as usize;
                price[classes]=price[classes].min(end);
            }
            let free=if first{pitch}else{mask&!(old<<1|old>>1)};
            let mut v=free;
            loop{
                let c=cost+(waiting&!v).count_ones() as usize+
                    if first{0}else{(v&!old&!(v<<1)&!1).count_ones() as usize};
                if c<=limit{
                    let mut p=std::array::from_fn(|i|i as u8);
                    for i in 0..k+w{p[i]=(part>>(4*i)&15) as u8}
                    let mut ok=true;
                    for i in 0..w{let j=k+w+i;
                        if (v|old)>>i&1!=0 && !join(&mut p,k+i,j) ||
                            i>0 && v>>(i-1)&3!=0 && !join(&mut p,j-1,j){ok=false;break}
                    }
                    if ok{let mut names=[31usize;32];let mut pk=0;
                        for i in 0..k+w{let root=rt(&p,if i<k{i}else{i+w});
                            if names[root]==31{names[root]=i}pk|=(names[root] as u64)<<(4*i)}
                        let st=(v,mask&!(1|(1<<(w-1)))&!(v|v<<1|v>>1|old),pk);
                        if best.get(&st).is_none_or(|&t|c<t){best.insert(st,c);bins[c].push((st,false))}
                    }
                }
                if v==0{break}v=(v-1)&free
            }
        }
    }
    println!("k={k} states={} lower bills by class count {:?}",best.len(),&price[1..]);
    if k<=3{assert!((1..=k).all(|i|price[i]>=i-1))}
    else{assert_eq!(&price[1..],&[0,1,2,2])}
}
