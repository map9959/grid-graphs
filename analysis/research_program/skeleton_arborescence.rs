//! Maximum weight grid tree oriented toward vertex zero. Bucket weights are
//! integers; contract all directed cycles of a best-parent assignment at once.
use std::io::{self,BufRead,Write};
#[derive(Clone,Copy)]
struct Arc { a:usize,b:usize,w:i64,old:usize }

fn arb(n:usize,root:usize,es:&[Arc])->Vec<usize>{
    let none=usize::MAX;
    let mut parent=vec![none;n];
    for (i,&e) in es.iter().enumerate(){
        if e.a!=root && (parent[e.a]==none||e.w>es[parent[e.a]].w){parent[e.a]=i;}
    }
    let mut id=vec![none;n];let mut seen=vec![none;n];let mut groups=0;
    for t in 0..n{
        let mut v=t;
        while v!=root && id[v]==none && seen[v]!=t{
            seen[v]=t;v=es[parent[v]].b;
        }
        if v!=root && id[v]==none && seen[v]==t{
            while id[v]==none{id[v]=groups;v=es[parent[v]].b;}
            groups+=1;
        }
    }
    if groups!=0{
        for x in &mut id{if *x==none{*x=groups;groups+=1}}
        let mut next=Vec::new();
        for (i,&e) in es.iter().enumerate(){
            if e.a!=root && id[e.a]!=id[e.b]{
                next.push(Arc{a:id[e.a],b:id[e.b],w:e.w-es[parent[e.a]].w,old:i});
            }
        }
        for j in arb(groups,id[root],&next){
            let i=next[j].old;parent[es[i].a]=i;
        }
    }
    parent.into_iter().filter(|&i|i!=none).collect()
}

fn main(){
    let parents=std::env::args().nth(1).as_deref()==Some("--parents");
    let mut lines=io::stdin().lock().lines().map(|s|s.unwrap());
    let hdr:Vec<usize>=lines.next().unwrap().split_whitespace().map(|s|s.parse().unwrap()).collect();
    let (n,e,k)=(hdr[0],hdr[1],hdr[2]);
    let mut es=Vec::new();let mut keys=Vec::new();
    for _ in 0..e{
        let a:Vec<usize>=lines.next().unwrap().split_whitespace().map(|s|s.parse().unwrap()).collect();
        es.push(Arc{a:a[0],b:a[1],w:0,old:0});keys.push(a[2]);
    }
    for l in lines{
        let w:Vec<i64>=l.split_whitespace().map(|s|s.parse().unwrap()).collect();assert_eq!(w.len(),k);
        for (a,&t) in es.iter_mut().zip(&keys){a.w=w[t]}
        let p=arb(n,0,&es);assert_eq!(p.len(),n-1);
        let mut to=vec![0;n];let mut counts=vec![0;k];
        for i in p{to[es[i].a]=es[i].b;counts[keys[i]]+=1}
        // Independently check the returned witness reaches NW from every vertex.
        let mut done=vec![false;n];done[0]=true;
        let mut seen=vec![n;n];
        for u in 0..n{
            let mut v=u;
            while !done[v]{assert_ne!(seen[v],u);seen[v]=u;v=to[v]}
            v=u;while !done[v]{done[v]=true;v=to[v]}
        }
        if parents{println!("{}",to.iter().map(|v|v.to_string()).collect::<Vec<_>>().join(" "))}
        else{println!("{}",counts.iter().map(|v|v.to_string()).collect::<Vec<_>>().join(" "))}
        io::stdout().flush().unwrap();
    }
}
