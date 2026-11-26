//! Exact-length necessary costs for 18-column caps, joining width-eleven windows.
#[path="cap_event_band.rs"] mod band;
use std::collections::HashMap;
const W:usize=11;
const CORE:u16=1022;
const BAD:u8=9;
struct Graph{keys:Vec<band::Key>,start:Vec<usize>,edges:Vec<Vec<(u32,u8)>>}
impl Graph{
 fn build(p:usize)->Self{
    let rails=(0..W).filter(|x|x%3==p).map(|x|1<<x).sum();
    let mut map=HashMap::new();let mut keys=vec![];let mut dist=vec![];let mut edges=vec![];
    let mut q=vec![vec![];9];let mut start=vec![];
    for (u,_) in band::options(W,(rails,0,0),CORE,true,p,None){
        let i=keys.len();map.insert(u,i);keys.push(u);dist.push(0);edges.push(vec![]);start.push(i);q[0].push(i)
    }
    for t in 0..9{while let Some(i)=q[t].pop(){
        if t!=dist[i]{continue}
        for (u,b) in band::options(W,keys[i],CORE,false,p,None){
            let z=t+b as usize;if z>=9{continue}
            let k=*map.entry(u).or_insert_with(||{let k=keys.len();keys.push(u);dist.push(9);edges.push(vec![]);k});
            edges[i].push((k as u32,b as u8));
            if z<dist[k]{dist[k]=z;q[z].push(k)}
        }
    }}
    println!("phase {p}: {} states, {} transitions",keys.len(),edges.iter().map(Vec::len).sum::<usize>());
    Self{keys,start,edges}
 }
 fn prices(&self,allow:&[Vec<bool>],cycle:bool)->Vec<Vec<u8>>{
    let h=allow.len();let n=self.keys.len();
    let mut fw=vec![vec![BAD;n];h];
    for &i in &self.start{if allow[0][self.keys[i].0 as usize]{fw[0][i]=0}}
    for j in 1..h{
      let (earlier,next)=fw.split_at_mut(j);
      for (i,&v) in earlier[j-1].iter().enumerate(){if v<BAD{for &(k,b) in &self.edges[i]{
        let k=k as usize;if allow[j][self.keys[k].0 as usize]{next[0][k]=next[0][k].min(v+b)}
      }}}
    }
    let mut bk:Vec<_>=self.keys.iter().map(|&(m,p,part)|{
      if cycle && (0..W).any(|i|(part>>(4*(i+1)))&15==0){BAD}
      else{(2*((CORE&!m).count_ones()+p.count_ones())).min(BAD.into()) as u8}
    }).collect();
    let mut ans=vec![vec![BAD;1<<W];h];
    for j in (0..h).rev(){
      for (i,&v) in fw[j].iter().enumerate(){let x=self.keys[i].0 as usize;ans[j][x]=ans[j][x].min(v+bk[i])}
      if j>0{let mut next=vec![BAD;n];for (i,&v) in fw[j-1].iter().enumerate(){if v<BAD{
        for &(k,b) in &self.edges[i]{let k=k as usize;if allow[j][self.keys[k].0 as usize]{next[i]=next[i].min(b+bk[k])}}
      }}bk=next}
    }
    ans
 }
}
fn main(){
 let h=std::env::args().nth(1).map(|v|v.parse().unwrap()).unwrap_or(22usize);
 let graphs:Vec<_>=(0..3).map(Graph::build).collect();let full=(1u32<<18)-1;
 let mut dom=vec![(0..=full).collect::<Vec<_>>();h];let mut cycle=false;
 loop{
   let mut allow=vec![vec![vec![false;1<<W];h];3];
   for (j,d) in dom.iter().enumerate(){for &m in d{let z=m|(m<<18);for x in 0..18{
      allow[(18-x)%3][j][((z>>x)&2047)as usize]=true
   }}}
   let costs:Vec<_>=graphs.iter().zip(&allow).map(|(g,a)|g.prices(a,cycle)).collect();
   let mut delta=0;
   for (j,d) in dom.iter_mut().enumerate(){
     let n=d.len();d.retain(|&m|{let z=m|(m<<18);(0..9).all(|x|{
       let c=&costs[(18-x)%3][j];
       c[((z>>x)&2047)as usize]+c[((z>>(x+9))&2047)as usize]<=12
     })});delta+=n-d.len()
   }
   println!("removed {delta}, row counts {:?}",dom.iter().map(Vec::len).collect::<Vec<_>>());
   if dom.iter().any(Vec::is_empty){println!("EMPTY");break}
   let newcycle=dom[h-1].iter().all(|&m| (m|((m<<1)|(m>>17)))&full==full);
   if delta==0 && newcycle==cycle{println!("OPEN");
      if std::env::args().any(|v|v=="--emit"){for d in &dom{println!("ROW {}",d.iter().map(u32::to_string).collect::<Vec<_>>().join(" "))}}
      break}cycle=newcycle
 }
}
