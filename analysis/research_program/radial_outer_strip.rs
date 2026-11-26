//! Optimize the projected radial core bound along one unrestricted outer side.
use std::collections::HashMap;
type S=(i32,u64,u16);
fn rt(p:&[usize;20],mut i:usize)->usize{while p[i]!=i{i=p[i]}i}
fn main(){
    let args:Vec<String>=std::env::args().skip(1).collect();
    let physical=args.get(1).map(String::as_str)==Some("4");
    let a:Vec<i32>=args.iter().take(if physical{2}else{args.len()}).map(|x|x.parse().unwrap()).collect();
    let d=a[0]as usize;assert!(d%3==0&&d>0&&d<=9);let w=d+1;let back=1<<d;let all=2*back-1;
    let num=|j:usize|args[j].parse::<i32>().unwrap();
    let labels=|j:usize|{let v:Vec<_>=args[j].bytes().map(|x|(x-b'0') as usize).collect();assert_eq!(v.len(),w);v};
    let init:S=if physical{let l=labels(4);(num(3),(0..w).map(|j|(l[j] as u64)<<(4*j)).sum::<u64>()|((num(9) as u64)<<40),num(5) as u16)}
        else{(-1,(0..w).map(|i|(i as u64)<<(4*i)).sum(),0)};
    let mut st=vec![init];let mut ix=HashMap::from([(init,0u32)]);let mut arcs=vec![];let mut starts=vec![];let mut i=0;
    while i<st.len(){starts.push(arcs.len());let (old,q,flags)=st[i];let free=if old<0{all}else{all&!(old<<1|old>>1)};
        let mut m=free;loop{
            let mut p=std::array::from_fn(|j|if j<w{(q>>(4*j)&15)as usize}else{j});
            let mut f:[bool;20]=std::array::from_fn(|j|j<w&&flags>>j&1!=0);f[2*w-1]=true;
            let mut anchor:[bool;20]=std::array::from_fn(|j|j<w&&q>>(40+j)&1!=0);
            let mut price=12*(m&(back-1)).count_ones()as i32-4*d as i32-4*i32::from(m&back==0)
                -4*i32::from(old>=0&&(old|m)&back==0)+6;
            let mut ok=true;for j in 0..w{
                for (u,edge) in [(j,old>=0&&(old|m)>>j&1!=0),(w+j-1,j>0&&m>>(j.saturating_sub(1))&3!=0)]{
                    if !edge{continue}let b=rt(&p,w+j);let c=rt(&p,u);if b==c{ok=false;break}
                    price-=6*i32::from(f[b]&&f[c]);f[b]|=f[c];anchor[b]|=anchor[c];p[c]=b;
                }if !ok{break}
            }
            if ok{
                let mut ids=[30;20];let mut part=0;let mut flag=0;
                for j in 0..w{let r=rt(&p,w+j);ids[r]=ids[r].min(j);part|=(ids[r]as u64)<<(4*j);part|=(anchor[r] as u64)<<(40+j);flag|=(f[r]as u16)<<j}
                let s=(m,part,flag);let n=st.len();let k=*ix.entry(s).or_insert(n as u32);
                if k as usize==n{st.push(s)}
                if a.get(1)==Some(&2){
                    assert_eq!(d,9);
                    let bad=![585,1,509,1021,9,489,1001,73,329,841].contains(&m);
                    price=a[2]*price+a[3]*i32::from(bad)
                }
                arcs.push((k,price as i16))
            }
            if m==0{break}m=(m-1)&free
        }i+=1
    }
    starts.push(arcs.len());
    if physical{
        let mut z=vec![i32::MIN;i];z[0]=0;
        for _ in 0..num(2){let mut v=vec![i32::MIN;i];for j in 0..i{if z[j]!=i32::MIN{
            for &(k,c) in &arcs[starts[j]..starts[j+1]]{v[k as usize]=v[k as usize].max(z[j]+c as i32)}
        }}z=v}
        let m=num(6);let r=labels(7);let mut best=i32::MIN;
        'state:for (j,&u) in z.iter().enumerate(){if u==i32::MIN{continue}let (old,q,flags)=st[j];
            let mut p=std::array::from_fn(|k|if k<w{(q>>(4*k)&15)as usize}else if k<2*w{w+r[k-w]}else{k});
            let mut f:[bool;20]=std::array::from_fn(|k|if k<w{flags>>k&1!=0}else{num(8)>>(k-w)&1!=0});
            let mut v=u-4*i32::from((old|m)&back==0);
            if q>>40!=0{let b=rt(&p,(q>>40).trailing_zeros() as usize);
                let c=w+num(10) as usize;assert!(f[b]&&f[c]);p[c]=b;
            }
            for k in 0..w{if (old|m)>>k&1==0{continue}let b=rt(&p,k);let c=rt(&p,w+k);
                if b==c{continue 'state}v-=6*i32::from(f[b]&&f[c]);p[c]=b;f[b]|=f[c];
            }best=best.max(v)
        }println!("{best}");return
    }
    if matches!(a.get(1),Some(1|3)){
        let mut f=vec![0;i];loop{let mut change=false;for j in 0..i{let u=f[j];
            for &(k,c) in &arcs[starts[j]..starts[j+1]]{let v=&mut f[k as usize];if *v<u+c as i32{*v=u+c as i32;change=true}}}
            if !change{break}}
        let mut out=vec![vec![];i];let mut rev=vec![vec![];i];
        for j in 0..i{for &(k,c) in &arcs[starts[j]..starts[j+1]]{let k=k as usize;if f[k]==f[j]+c as i32{out[j].push(k);rev[k].push(j)}}}
        fn dfs(j:usize,adj:&[Vec<usize>],used:&mut [bool],order:&mut Vec<usize>){
            if used[j]{return}used[j]=true;
            for &k in &adj[j]{dfs(k,adj,used,order)}order.push(j)
        }
        let mut used=vec![false;i];let mut order=vec![];for j in 0..i{dfs(j,&out,&mut used,&mut order)}
        let mut cycles=std::collections::BTreeSet::new();
        let mut critical=vec![];
        used.fill(false);for j in order.into_iter().rev(){if !used[j]{let mut s=vec![];dfs(j,&rev,&mut used,&mut s);
            if s.len()>1||out[j].contains(&j){let mut masks:Vec<_>=s.iter().map(|&v|st[v].0).collect();masks.sort();masks.dedup();
                critical.extend(s.iter().copied());
                if s.len()<=6{for &start in &s{
                    let mut paths=vec![vec![start]];
                    while let Some(p)=paths.pop(){for &k in &out[*p.last().unwrap()]{
                        if k==start{let mut w:Vec<_>=p.iter().map(|&j|st[j].0).collect();let mut best=w.clone();
                            for _ in 1..w.len(){w.rotate_left(1);best=best.min(w.clone())}cycles.insert(best);
                        }else if s.contains(&k)&&!p.contains(&k){let mut t=p.clone();t.push(k);paths.push(t)}
                    }}
                }}else{println!("large critical class {} {:?}",s.len(),masks);}
            }
        }}
         println!("critical cycles of masks: {cycles:?}");
         if a.get(1)==Some(&3){
             // Max-plus potentials turn longest walks into shortest
             // nonnegative-debit paths. Keep each phase/partition as a
             // separate endpoint; path interiors may use any column.
             use std::cmp::Reverse;
             use std::collections::BinaryHeap;
             critical.sort_by_key(|&j|st[j]);
             let shortest=|seeds:&[(usize,i32)]|{
                 let mut dis=vec![i32::MAX;i];let mut heap=BinaryHeap::new();
                 for &(j,u) in seeds{dis[j]=u;heap.push(Reverse((u,j)))}
                 while let Some(Reverse((u,j)))=heap.pop(){if u!=dis[j]{continue}
                     for &(k,c) in &arcs[starts[j]..starts[j+1]]{let k=k as usize;
                         let step=f[k]-f[j]-c as i32;assert!(step>=0);
                         let v=u+step;if v<dis[k]{dis[k]=v;heap.push(Reverse((v,k)))}
                     }
                 }dis
             };
             let prefix=shortest(&[(0,0)]);
             let mut raw=vec![];let mut ends=vec![];
             for &j in &critical{
                 let dis=shortest(&[(j,0)]);
                 raw.push(critical.iter().map(|&k|f[k]-f[j]-dis[k]).collect::<Vec<_>>());
                 ends.push((0..i).filter(|&k|dis[k]!=i32::MAX).map(|k|f[k]-f[j]-dis[k]).max().unwrap());
             }
             println!("masks {:?}",critical.iter().map(|&j|st[j].0).collect::<Vec<_>>());
             println!("prefix {:?}",critical.iter().map(|&j|f[j]-f[0]-prefix[j]).collect::<Vec<_>>());
             println!("suffix {:?}",ends);
             for row in raw{println!("transfer {:?}",row)}
         }
        return
    }
    let mut seen=HashMap::new();let mut z=vec![i32::MIN;i];z[0]=0;let mut peak=0;
    for h in 1..=200{
        let mut v=vec![i32::MIN;i];for j in 0..i{if z[j]==i32::MIN{continue}
            for &(k,c) in &arcs[starts[j]..starts[j+1]]{let u=&mut v[k as usize];*u=(*u).max(z[j]+c as i32)}}
        let mx=*v.iter().max().unwrap();peak=peak.max(mx);
        let sig:Vec<_>=v.iter().map(|&x|if x==i32::MIN{i32::MIN}else{x-mx}).collect();
        if let Some((j,b))=seen.insert(sig,(h,mx)){println!("depth {d}: {i} states, {} arcs, normalized {j}..{h} increment {}, peak {peak}",arcs.len(),mx-b);return}z=v
    }panic!("no recurrence")
}
