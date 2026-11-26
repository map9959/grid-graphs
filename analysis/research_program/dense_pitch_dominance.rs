//! Two pitch cuts in the eight outer sites. Retain their SIX physical
//! terminal labels and the common side-nine tree for arbitrary gluing.
use std::collections::HashMap;
const W:usize=8;const P:u8=146; // physical depths 6,3,0, from the backing end
const CUT:i8=-11;
type S=(u8,u64);
type Table=HashMap<(u32,u16,u8),i8>;
#[derive(Clone,Copy)]
struct Edge{next:u32,score:i8,map:u64}
fn root(p:&[usize;17],mut i:usize)->usize{while p[i]!=i{i=p[i]}i}
fn link(p:&mut [usize;17],a:usize,b:usize)->bool{
    let a=root(p,a);let b=root(p,b);p[a]=b;a!=b
}
fn transitions((old,part):S,back:bool)->Vec<(S,u64)>{
    let free=!(old<<1|old>>1);let mut v=free;let mut out=vec![];
    loop{
        let mut p=std::array::from_fn(|i|i);
        for i in 0..W{p[i]=((part>>(4*i))&15)as usize;}
        let r=((part>>32)&15)as usize;if r<W{p[16]=r}
        let ok=(0..W).all(|i|((old|v)>>i&1==0||link(&mut p,i,W+i))&&
            (i==0||v>>(i-1)&3==0||link(&mut p,W+i-1,W+i)))&&
            (!back||v&1==0||link(&mut p,16,W));
        if ok{
            let mut ids=[15;17];let mut q=0;let mut map=0;
            for j in 0..=W{let r=root(&p,W+j);ids[r]=ids[r].min(j);q|=(ids[r]as u64)<<(4*j);}
            // 9..=15 cannot encode every dead component; mark absent by
            // 15 and use its previous canonical class at transport time.
            for j in 0..=W{let r=root(&p,if j==W{16}else{j});map|=(ids[r]as u64)<<(4*j);}
            out.push(((v,q),map));
        }
        if v==0{break}v=(v-1)&free;
    }out
}
fn transport(k:u16,map:u64)->u16{
    let mut ids=[0;3];let mut out=0;
    for j in 0..3{
        let x=((k>>(4*j))&15)as usize;
        let nx=if x<=8{((map>>(4*x))&15)as usize}else{15};
        if nx<15{ids[j]=nx;out|=(nx as u16)<<(4*j)}
        else{
            // Distinguish previously dead classes from distinct live
            // classes that have just died (old IDs of either kind are unique).
            ids[j]=16+x;let pos=ids[..=j].iter().position(|&t|t==ids[j]).unwrap();
            out|=((9+pos)as u16)<<(4*j);
        }
    }out
}
fn groups(m:u8)->Vec<usize>{(0..8).filter(|&i|m>>i&1!=0).collect()}
fn initial(mask:u8,backed:bool)->(S,u16){
    let mut par=std::array::from_fn(|j|j);
    for i in 0..7{if mask>>i&3!=0{link(&mut par,i,i+1);}}
    if backed&&mask&1!=0{link(&mut par,0,8);}
    let ids:Vec<_>=(0..9).map(|i|(0..=i).find(|&j|root(&par,i)==root(&par,j)).unwrap()).collect();
    let q=ids.iter().enumerate().map(|(i,&v)|(v as u64)<<(4*i)).sum();
    let g=groups(mask);assert_eq!(g.len(),3);
    ((mask,q),(ids[g[0]]+16*ids[g[1]]+256*ids[g[2]])as u16)
}
fn graph(first:u8,backed:bool,both:bool)->(Vec<S>,Vec<[Vec<Edge>;2]>){
    let mut st=vec![initial(first,backed).0];if both&&initial(first,false).0!=st[0]{st.push(initial(first,false).0)}
    let mut ix:HashMap<_,_>=st.iter().enumerate().map(|(i,&s)|(s,i as u32)).collect();let mut adj=vec![];
    let mut i=0;
    while i<st.len(){
        adj.push(std::array::from_fn(|j|{
            transitions(st[i],j!=0).into_iter().map(|(s,map)|{
                let n=st.len();let v=*ix.entry(s).or_insert(n as u32);if v as usize==n{st.push(s)}
                Edge{next:v,score:s.0.count_ones()as i8-3,map}
            }).collect()
        }));i+=1
    }(st,adj)
}
fn step(d:&Table,adj:&[[Vec<Edge>;2]],opened:bool,cool:u8,scale:i8,st:&[S])->Table{
    let mut nd=Table::new();
    for (&(i,k,age),&v) in d{
        for back in 0..=1{if back==0&&(!opened||age<cool){continue}
            for &e in &adj[i as usize][back]{
                let z=v+scale*e.score+((scale==9&&st[e.next as usize].0!=P)as i8);
                if z<if scale==9{-100}else{CUT}{continue}
                let t=(e.next,transport(k,e.map),if back==0{0}else{(age+1).min(cool)});
                let ent=nd.entry(t).or_insert(i8::MIN);*ent=(*ent).max(z);
            }
        }
    }nd
}
fn prices(d:&Table,st:&[S],last:u8)->HashMap<[u8;7],i8>{
    let mut result=HashMap::new();
    let g=groups(last);assert_eq!(g.len(),3);
    for (&(i,k,_),&v) in d{
        let (m,q)=st[i as usize];if m!=last{continue}
        let ids=[((q>>32)&15)as u8,(k&15)as u8,((k>>4)&15)as u8,(k>>8)as u8,
                 ((q>>(4*g[0]))&15)as u8,((q>>(4*g[1]))&15)as u8,((q>>(4*g[2]))&15)as u8];
        let p=std::array::from_fn(|i|ids.iter().position(|x|*x==ids[i]).unwrap()as u8);
        let ent=result.entry(p).or_insert(i8::MIN);*ent=(*ent).max(v);
    }result
}
fn dominates(p:&[u8;7],q:&[u8;7])->bool{(0..7).all(|i|(0..i).all(|j|p[i]!=p[j]||q[i]==q[j]))}
fn partitions(i:usize,m:u8,p:&mut [u8;7],out:&mut Vec<[u8;7]>){
    if i==7{out.push(*p);return}
    for j in 0..=m{p[i]=j;partitions(i+1,m.max(j+1),p,out)}
}
fn compat(p:&[u8;7],e:&[u8;7])->bool{
    let mut q=std::array::from_fn(|i|i);
    for i in 0..7{if !link(&mut q,p[i]as usize,7+e[i]as usize){return false}}
    true
}
fn main(){
    let gap=std::env::args().nth(1).map(|s|s.parse::<u8>().unwrap()).unwrap_or(3);
    let buffer=std::env::args().nth(2).map(|s|s.parse::<usize>().unwrap()).unwrap_or(3);
    let mask=|i|std::env::args().nth(i).map(|s|s.parse::<u8>().unwrap()).unwrap_or(P);
    let first=mask(4);let end=mask(5);
    let free=std::env::args().nth(3).as_deref()==Some("free-ends");
    let both=std::env::args().nth(3).as_deref()==Some("physical-ends");
    let standard=first==P&&end==P;
    let scale=if std::env::args().nth(3).as_deref()==Some("weighted"){9}else{1};
    assert!(scale==1||gap>=4);
    assert!((3..=16).contains(&gap)&&buffer>=1);let cool=gap-1;
    let (st,adj)=graph(first,!free,both);let (_,k)=initial(first,!free);let mut c=HashMap::from([((0,k,cool),0)]);let mut o=c.clone();
    let mut last:Vec<(Table,Table)>=vec![];let mut worst=0;
    let mut ext=vec![];partitions(1,1,&mut [0;7],&mut ext);
    let mut extloss=0;let mut planar=0;let mut ranks=[-100i8;6];let mut wired_ranks=[-100i8;7];
    // 1 pitch row + two backed guard rows + arbitrary interior +
    // two backed guard rows + 1 final pitch row (also backed).
    for _ in 1..buffer{c=step(&c,&adj,false,cool,scale,&st);}o.clone_from(&c);
    if both{assert!(buffer==1&&scale==1);let (s,k)=initial(first,false);
        o.insert((st.iter().position(|&t|t==s).unwrap()as u32,k,0),0);}
    for h in 0..80{
        let close=|d:&Table|{
            let mut e=d.clone();for j in 0..buffer{
                if free&&j+1==buffer {
                    let mut out=Table::new();
                    for (&(i,k,_),&v) in &e{for e in &adj[i as usize][0]{
                        if st[e.next as usize].0!=end{continue}
                        let ent=out.entry((e.next,transport(k,e.map),0)).or_insert(i8::MIN);
                        *ent=(*ent).max(v+e.score)
                    }}
                    e=out;
                }else if both&&j+1==buffer{
                    let mut out=Table::new();
                    for (&(i,k,age),&v) in &e{for b in 0..2{
                        if b==0&&age<cool{continue}
                        for e in &adj[i as usize][b]{
                            if st[e.next as usize].0!=end{continue}
                            let ent=out.entry((e.next,transport(k,e.map),0)).or_insert(i8::MIN);
                            *ent=(*ent).max(v+e.score)
                        }
                    }}
                    e=out;
                }else{e=step(&e,&adj,false,cool,scale,&st)}
            }
            prices(&e,&st,end)
        };
        let cp=close(&c);let op=close(&o);
        for (p,&z) in &op{
            let groups=p[1..].iter().copied().collect::<std::collections::HashSet<_>>().len();
            ranks[6-groups]=ranks[6-groups].max(z);
            let k=7-p.iter().copied().collect::<std::collections::HashSet<_>>().len();
            wired_ranks[k]=wired_ranks[k].max(z);
        }
        for (q,v) in op.iter().filter(|_|scale==1&&standard&&!free&&!both){
            if *v<=-6{continue}
            let best=cp.iter().filter(|(p,_)|dominates(p,q)).map(|(_,v)|*v).max().unwrap_or(-6).max(-6);
            worst=worst.max(v-best);
        }
        let mut leaks=0;let mut simple=usize::MAX;let mut example=[0;7];let mut top_loss=-100;
        for e in ext.iter().filter(|_|scale==1&&standard&&!free&&!both){
            let best=|tab:&HashMap<[u8;7],i8>|tab.iter().filter(|(p,_)|compat(p,e)).map(|(_,v)|*v).max().unwrap_or(-6).max(-6);
            let oz=best(&op);let diff=oz-best(&cp);extloss=extloss.max(diff);
            if diff>0{top_loss=top_loss.max(oz)}
            // 0=root, 1..3 along the initial cut (back to rim),
            // and the final cut traversed in reverse in the exterior.
            let ord=[0,1,2,3,6,5,4];let mut nc=true;
            for a in 0..7{for b in a+1..7{for c in b+1..7{for d in c+1..7{
                if e[ord[a]]==e[ord[c]]&&e[ord[b]]==e[ord[d]]&&e[ord[a]]!=e[ord[b]]{nc=false}
            }}}}
            if nc{planar=planar.max(diff);if diff>0{leaks+=1;let joins=6-*e.iter().max().unwrap() as usize;if joins<simple{simple=joins;example=*e;}}}
        }
        if h%5==0{println!("interior {h}: {} {} prefixes, worst loss {worst}, vulnerable planar exteriors {leaks} best defective excess {top_loss} simplest {example:?}",c.len(),o.len());}
        if let Some(j)=last.iter().position(|(x,y)|x==&c&&y==&o){
            if standard&&gap==3&&buffer==1&&!free&&!both{assert_eq!(ranks,[-4,-2,-1,0,0,0]);assert_eq!((worst,extloss,planar),(2,1,1));}
            if standard&&scale==9&&gap==4&&buffer==1{assert_eq!(ranks,[-22,-11,-3,3,9,12]);}
            println!("complete normalized recurrence {} -> {h}, uniform refining loss {worst}, exterior loss {extloss}, noncrossing {planar}",h-last.len()+j);
            println!("strip excess by terminal rank: {ranks:?}; retaining backing root: {wired_ranks:?}");return;
        }
        if last.len()==if scale==9{18}else{4}{last.remove(0);}
        last.push((c.clone(),o.clone()));c=step(&c,&adj,false,cool,scale,&st);o=step(&o,&adj,true,cool,scale,&st)
    }panic!("no recurrence");
}
