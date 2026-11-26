//! Minimum localized endpoint/color bill in an arbitrary-height wired pitch cap.
use std::collections::{BinaryHeap,HashMap,HashSet};
use std::sync::Arc;
use std::cmp::Reverse;
#[derive(Clone,Copy,Hash,PartialEq,Eq,PartialOrd,Ord)]
struct State {up:u64,m:u64,part:[u8;64],stage:u8}
fn root(p:&[usize;128],mut j:usize)->usize{while p[j]!=j{j=p[j]}j}
fn join(p:&mut[usize;128],flag:&mut[u8;128],a:usize,b:usize)->bool{
    let i=root(p,a);let j=root(p,b);if i==j{return false}p[i]=j;flag[j]|=flag[i];true
}
type Edge=(u64,u64,u64);
#[derive(Clone)]
struct Filter {shift:usize,mask:u64,inner:u64,arcs:Arc<HashSet<Edge>>,opts:Arc<HashMap<(u64,u64),Vec<u64>>>,ends:Arc<HashSet<(u64,u64)>>}
fn solve(k:usize,lim:i32,limit:usize,trace:bool,cuts:&[Filter])->Option<Filter>{
    let w=3*k+2;assert!(w<64);let all=u64::MAX>>(64-w);let inner=(all>>1)&!1;
    let pitch=(0..w).filter(|j|j%3==2).fold(0u64,|a,j|a|(1<<j));let pitch=pitch&inner;
    let two=std::env::var_os("PITCH_TWO").is_some();
    let mut s=State{up:0,m:if two{0}else{pitch},part:[0;64],stage:0};
    // Artificial pitch row: contract every tooth with the common root.
    // The unoccupied halo endpoints need not be connected to the root.
    for j in 0..=w{
        let v=if j<w&&inner>>j&1==0{j}else{w};
        s.part[j]=if two{j as u8|if j==0||j>=w-1{128}else{0}}else{(v|128)as u8};
    }
    let mut st=HashMap::from([(s,0)]);let mut queue=BinaryHeap::from([Reverse((0,s))]);
    let ranked=std::env::var_os("PITCH_RANK").is_some();
    let scale=if ranked{std::env::var("PITCH_SCALE").map(|s|s.parse().unwrap()).unwrap_or(5)}else{1};
    let debit:i32=std::env::var("PITCH_DEBIT").map(|s|s.parse().unwrap()).unwrap_or(4);
    let mut sources=vec![(s,0,0)];
    if ranked{
        let fixed=std::env::var("PITCH_DROP").ok().map(|s|s.parse::<u64>().unwrap());
        if fixed.is_some_and(|x|x!=0){st.clear();queue.clear();sources.clear()}
        for drop in 1u64..1<<k{
            if fixed.is_some_and(|v|v!=drop){continue}
            let fee=debit*drop.count_ones()as i32;if fee>lim{continue}
            let mut t=s;for j in 0..k{if drop>>j&1!=0{for i in 1+3*j..4+3*j{t.part[i]=(1+3*j)as u8|64}}}
            st.insert(t,fee);queue.push(Reverse((fee,t)));sources.push((t,fee,drop));
        }
    }
    let mut edges=Vec::new();let mut end=HashMap::new();let mut tails=std::collections::BTreeMap::new();
    let tails_only=std::env::var_os("PITCH_TAILS").is_some()&&!trace;
    let witness=std::env::var_os("PITCH_WITNESS").is_some()&&!trace;
    let guard=if !trace{match std::env::var("PITCH_EDGE").as_deref(){Ok("L")=>3,Ok("R")=>3<<(w-2),Ok("LR")=>3|3<<(w-2),_=>0}}else{0};
    let mut pred=HashMap::new();let mut win=None;
    let mut best=lim+1;
    while let Some(Reverse((z,s)))=queue.pop(){
        if z>=best&&!trace&&!tails_only{break}if st.get(&s)!=Some(&z){continue}
        let m=s.m;let pa=std::array::from_fn(|j|if j<=w{(s.part[j]&63)as usize}else{j});
        let stage=(s.stage as u64)<<63;
        if two&&m==pitch&&s.stage==0{
            let t=State{stage:1,..s};
            if trace{edges.push((s,t,0))}
            if !st.contains_key(&t)||st[&t]>z{st.insert(t,z);queue.push(Reverse((z,t)))}
        }
        let mut flags=[0u8;128];for j in 0..=w{flags[pa[j]]|=s.part[j]>>6}
        let bare=inner&!m;let lat=(m<<1)|(m>>1);let hjoin=(m<<1)&(m>>1);
        let isolated=bare&!(lat|s.up);let doub=bare&!pitch;
        let price=|v:u64|{
            (isolated&!v).count_ones()+(isolated&pitch&!v).count_ones()+
            (doub&(hjoin|(s.up&v))).count_ones()
        };
        // Finish before inserting the next row. Every bottom tooth is
        // in a separate class, disjoint from every top contact.
        if (!two||s.stage==1&&m==0)&&m&(m<<1|m<<2)==0&&(trace||std::env::var_os("PITCH_BLANK_END").is_none()||m==0)&&cuts.iter().all(|c|c.ends.contains(&(stage|((s.up>>c.shift)&c.inner),(m>>c.shift)&c.mask))){
            let mut seen=0u64;let mut ok=true;
            for j in 0..w{if m>>j&1!=0{let r=pa[j];if r==pa[w]||seen>>r&1!=0{ok=false;break}seen|=1<<r}}
            if !trace&&std::env::var_os("PITCH_NO_RETURN").is_some(){
                if (1..w-1).any(|j|s.up>>j&1!=0&&pa[j]==pa[w]){ok=false}
            }
            if ok{
                let extra=(0..=w).filter(|&j|pa[j]==j&&flags[j]==1&&seen>>j&1==0).count();
                let cost=scale*((price(0)+(m&inner&!pitch).count_ones())as i32+2*extra as i32);
                if z+cost<best{win=Some(s);best=z+cost}
                if trace&&z+cost<=lim{end.insert(s,cost);}
                if tails_only&&z+cost<=lim{
                    let key:Vec<_>=(0..k).map(|i|((m>>(1+3*i))&7)+8*((s.up>>(1+3*i))&7)).collect();
                    let e=tails.entry(key).or_insert(lim+1);*e=(*e).min(z+cost)
                }
            }
        }
        let free=all&!lat&!guard;let mut fixed=0;let mut opts=vec![0u64];
        if !cuts.is_empty(){
            for c in cuts{let msk=c.mask<<c.shift;
                let key=(stage|((s.up>>c.shift)&c.inner),(m>>c.shift)&c.mask);
                let mut next=vec![];if let Some(allow)=c.opts.get(&key){for a in opts{for &v in allow{let b=v<<c.shift;if (a^b)&fixed&msk==0&&b&!free==0{next.push(a|b)}}}}
                opts=next;fixed|=msk;
            }
            assert_eq!(fixed,all);
        }else{opts.clear();let mut v=free;loop{opts.push(v);if v==0{break}v=(v-1)&free}}
        for v in opts{
            let hor=(v<<1)|(v>>1);
            let starts=(if two&&s.stage==0{m&pitch&!lat&!v}else{v&pitch&!hor&!m}).count_ones()*2+
                (v&pitch&((v<<1)^(v>>1))).count_ones();
            let mut val=z+scale*(price(v)+starts)as i32;
            if val<=lim&&(trace||tails_only||val<best)&&cuts.iter().all(|c|c.arcs.contains(&(stage|((s.up>>c.shift)&c.inner),(m>>c.shift)&c.mask,(v>>c.shift)&c.mask))){
                let mut p=pa;let mut f=flags;let mut ok=true;
                for j in 0..w{
                    let a=w+1+j;f[a]=((v>>j)&1)as u8|if j==0||j+1==w{2}else{0};
                    if (m|v)>>j&1!=0&&!join(&mut p,&mut f,j,a){ok=false;break}
                    if j>0&&v>>(j-1)&3!=0&&!join(&mut p,&mut f,a-1,a){ok=false;break}
                }
                if ok{
                    let mut reps=[128;128];let mut key=[0;64];
                    for j in 0..=w{
                        let r=root(&p,if j==w{w}else{w+1+j});reps[r]=reps[r].min(j);
                        key[j]=reps[r]as u8|(f[r]<<6)
                    }
                    val+=2*scale*(0..=w).filter(|&j|p[j]==j&&reps[j]==128&&f[j]==1).count()as i32;
                    if val<=lim&&(trace||tails_only||val<best){
                        let t=State{up:m&!v&inner,m:v,part:key,stage:s.stage};
                        if trace{edges.push((s,t,val-z))}
                        if st.get(&t).is_none_or(|&a|a>val){
                            if witness{pred.insert(t,s);}
                            st.insert(t,val);queue.push(Reverse((val,t)));
                            if st.len()>limit{println!("window {k}: state limit at settled bill {z}");return None}
                        }
                    }
                }
            }
        }
    }
    println!("window {k} pitch triples, all heights: min(bill,{})={best}, {} states",lim+1,st.len());
    if witness{if let Some(mut q)=win{let mut path=vec![q.m];while let Some(&p)=pred.get(&q){q=p;path.push(q.m)}
        for m in path.into_iter().rev(){println!("{}",(0..w).map(|j|if m>>j&1!=0{'#'}else{'.'}).collect::<String>())}}}
    if tails_only{for (v,z) in tails{println!("tail {v:?} {z}")}}
    if !trace{return None}
    let mut rem=end.clone();loop{let mut changed=false;
        for &(a,b,v) in &edges{if let Some(&q)=rem.get(&b){if st[&a]+q+v<=lim&&rem.get(&a).is_none_or(|&p|p>q+v){
            rem.insert(a,q+v);changed=true}}}if !changed{break}}
    let arcs:HashSet<_>=edges.iter().filter(|(a,b,v)|a.stage==b.stage&&rem.get(b).is_some_and(|&q|st[a]+q+v<=lim)).map(|(a,b,_)|(a.up|((a.stage as u64)<<63),a.m,b.m)).collect();
    if let Ok(nfa)=std::env::var("PITCH_NFA"){
        let args:Vec<_>=nfa.split(',').map(|a|a.parse::<usize>().unwrap()).collect();
        if args[0]==k&&args[1]==lim as usize{
            let mask=(1u64<<(2+3*args[2]))-1;let shift=3*(k-args[2]);
            let mut ids=HashMap::new();let mut initial=vec![];
            for &(q,z,drop) in &sources{if rem.get(&q).is_some_and(|&v|v+z<=lim){
                let n=ids.len();let i=*ids.entry((q,z)).or_insert(n);initial.push((i,drop));
            }}
            let mut wire=std::collections::BTreeSet::new();let mut finalset=std::collections::BTreeSet::new();
            for (a,b,v) in &edges{if let Some(&q)=rem.get(b){for z in st[a]..=lim-q-v{
                let n=ids.len();let i=*ids.entry((*a,z)).or_insert(n);
                let n=ids.len();let j=*ids.entry((*b,z+v)).or_insert(n);
                let f=u64::from(a.stage!=b.stage)<<63;
                wire.insert((i,f|(b.m&mask),f|(b.m>>shift),j,f|b.m));
            }}}
            for (q,c) in &end{for z in st[q]..=lim-c{if let Some(&i)=ids.get(&(*q,z)){finalset.insert(i);}}}
            println!("NFA {} {}",ids.len(),wire.len());
            for (i,drop) in initial{println!("i {i} {drop}")}
            for (i,a,b,j,m) in wire{println!("e {i} {a} {b} {j} {m}")}
            for i in finalset{println!("f {i}")}
        }
    }
    let mut opts:HashMap<_,Vec<_>>=HashMap::new();for &(a,b,c) in &arcs{opts.entry((a,b)).or_default().push(c)}
    Some(Filter{shift:0,mask:all,inner,arcs:Arc::new(arcs),opts:Arc::new(opts),ends:Arc::new(end.keys().map(|a|(a.up|((a.stage as u64)<<63),a.m)).collect())})
}
fn lb(k:usize)->i32{
    // For 7 and 8, see the explicit independent checks in pitch_endpoint_windows.py.
    let mut lo=[0,0,1,2,2,3,4,5,6];
    if std::env::var_os("PITCH_TWO").is_some()||std::env::var_os("PITCH_RANK").is_some(){lo[7]=4;lo[8]=5}
    if k<lo.len(){return lo[k]}
    if std::env::var_os("PITCH_TWO").is_some(){if k==10{return 7}if k==11{return 8}}
    (1..k).map(|i|lb(i)+lb(k-i)).max().unwrap()
}
fn filters(k:usize,b:i32,limit:usize,memo:&mut HashMap<(usize,i32),Filter>)->Vec<Filter>{
    if k<=2{return vec![]}
    let mut keys=vec![];
    for len in 2..k{
        for left in 0..=k-len{let room=b-lb(left)-lb(k-len-left);
            if room>=0&&room<=lb(len)+2&&len<=8{keys.push((room-lb(len),len,left,room))}
        }
    }
    keys.sort_by_key(|&(slack,len,left,_)|(slack,len,left));let mut cuts=vec![];let mut cover=0u64;
    for (slack,len,left,room) in keys{
        let mask=((1<<len)-1)<<left;
        let balanced=len>=k/2&&len<=k.div_ceil(2)+1&&(left==0||left+len==k);
        if slack>0&&cover&mask==mask&&!balanced{continue}
        if !memo.contains_key(&(len,room)){
            let small=filters(len,room,limit,memo);let f=solve(len,room,limit,true,&small).unwrap();
            memo.insert((len,room),f);
        }
        let mut f=memo[&(len,room)].clone();f.shift=3*left;cover|=mask;cuts.push(f)
    }
    if cover!=(1<<k)-1{return vec![]}cuts
}
fn main(){let v:Vec<usize>=std::env::args().skip(1).map(|x|x.parse().unwrap()).collect();
    let mut cuts=vec![];let limit=*v.get(2).unwrap_or(&2_000_000);
    if std::env::var_os("PITCH_AUTO").is_some(){
        let f=filters(v[0],v[1]as i32,limit,&mut HashMap::new());
        assert!(v[0]<=3||!f.is_empty());solve(v[0],v[1]as i32,limit,false,&f);return
    }
    if v.len()>3{for chunk in v[3..].chunks_exact(3){
        let mut sub=vec![];
        if std::env::var_os("PITCH_FILTER_AUTO").is_some(){sub=filters(chunk[0],chunk[1]as i32,limit,&mut HashMap::new())}
        else if chunk[0]>=4&&chunk[1]==chunk[0]-2{
            for (a,b,j) in if chunk[0]==4{vec![(2,1,0),(2,1,2),(3,2,0),(3,2,1)]}
                else{assert_eq!(chunk[0],5);vec![(2,1,0),(3,2,2),(3,2,0),(2,1,3)]}{
                let mut c=solve(a,b,limit,true,&[]).unwrap();c.shift=3*j;sub.push(c)
            }
        }
        let mut c=solve(chunk[0],chunk[1]as i32,limit,true,&sub).unwrap();
        c.shift=3*chunk[2];println!("filter width {} at {}, {} positive-support arcs",chunk[0],chunk[2],c.arcs.len());cuts.push(c)
    }}
    solve(v[0],v[1]as i32,limit,std::env::var_os("PITCH_NFA").is_some(),&cuts);}
