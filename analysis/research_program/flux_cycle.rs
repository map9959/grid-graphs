//! Exact integer cycle separation / difference-potential replay. Stream graphs once.
use std::io::{self,BufRead,Write};
fn nums(r:&mut impl BufRead)->Option<Vec<i128>>{let mut s=String::new();if r.read_line(&mut s).unwrap()==0{None}else{Some(s.split_whitespace().map(|v|v.parse().unwrap()).collect())}}
struct G{n:usize,arcs:Vec<(usize,usize,i64,i64,i64)>}
fn run(g:&G,w:&[i128])->Vec<usize>{
    let mut f=vec![0i128;g.n];let mut pred=vec![usize::MAX;g.n];
    loop{
        let mut changed=false;
        for (i,&(u,v,_,_,_)) in g.arcs.iter().enumerate(){let z=f[u]+w[i];if z>f[v]{f[v]=z;pred[v]=i;changed=true}}
        if !changed{assert!(g.arcs.iter().enumerate().all(|(i,&(u,v,_,_,_))|f[v]>=f[u]+w[i]));return vec![]}
        let mut seen=vec![usize::MAX;g.n];
        for i in 0..g.n{let mut j=i;while seen[j]==usize::MAX&&pred[j]!=usize::MAX{seen[j]=i;j=g.arcs[pred[j]].0}
            if seen[j]==i{let at=j;let mut path=vec![];loop{let e=pred[j];path.push(e);j=g.arcs[e].0;if at==j{break}}
                if path.iter().map(|&k|w[k]).sum::<i128>()>0{return path}
            }
        }
    }
}
fn main(){let mut r=io::BufReader::new(io::stdin().lock());let ng=nums(&mut r).unwrap()[0];let mut gs=vec![];
    for _ in 0..ng{let h=nums(&mut r).unwrap();let mut arcs=vec![];for _ in 0..h[1]{
        let a=nums(&mut r).unwrap();arcs.push((a[0]as usize,a[1]as usize,a[2]as i64,a[3]as i64,a[4]as i64))}
        gs.push(G{n:h[0]as usize,arcs})
    }
    while let Some(a)=nums(&mut r){let n=a[0]as usize;let scale=a[1];let v=&a[2..];
        for (j,g) in gs.iter().enumerate(){let t=if j>0{v[n+j-1]}else{0};
            let tol=v.get(n+2).copied().unwrap_or(0);
            let w:Vec<_>=g.arcs.iter().map(|&(_,_,c,p,m)|c as i128*scale+(if p>=0{v[p as usize]}else{0})-(if m>=0{v[m as usize]}else{0})-t-tol).collect();
            let cycle=run(g,&w);print!("{}",cycle.len());for k in cycle{print!(" {k}")}println!()
        }io::stdout().flush().unwrap()
    }
}
