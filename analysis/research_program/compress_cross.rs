//! Remove one row and one column, billing the actual nullity before cycle repair.
use std::io::{self,Read};
fn rt(par:&mut [usize],mut i:usize)->usize{while par[i]!=i{par[i]=par[par[i]];i=par[i]}i}
fn null(a:&[bool],s:usize)->usize{
    let mut p:Vec<_>=(0..s*s).collect();let mut b=0;
    for i in 0..a.len(){for j in [if i%s>0{i-1}else{i},if i>=s{i-s}else{i}]{
        if i==j||!a[i]&&!a[j]{continue}let u=rt(&mut p,i);let v=rt(&mut p,j);
        if u==v{b+=1}else{p[u]=v}
    }}b
}
fn main(){
    let mut txt=String::new();io::stdin().read_to_string(&mut txt).unwrap();let rows:Vec<_>=txt.split_whitespace().map(str::as_bytes).collect();
    let n=rows.len();let s=n-1;let total=rows.iter().flat_map(|v|v.iter()).filter(|&&b|b==b'#').count();
    let mut best=(usize::MAX,0,0,0,0);let mut mm=vec![];
    for y in 0..n{for x in 0..n{
        let cost=rows[y].iter().filter(|&&b|b==b'#').count()+(0..n).filter(|&i|i!=y&&rows[i][x]==b'#').count();
        if cost>=best.0{continue}
        let mut a=vec![false;s*s];
        for i in 0..s{for j in 0..s{a[i*s+j]=rows[i+usize::from(i>=y)][j+usize::from(j>=x)]==b'#'}}
        let b=null(&a,s);if cost+b<best.0{best=(cost+b,y,x,cost,b);mm=a}
    }}
    let(c,y,x,deleted,mut b)=best;let mut repairs=0;
    while b>0{
        // Test actual deletions. Some remove several cycles. At a
        // marked turn a unit face has a singly owned edge, since no
        // compressed unit face can have four marked corners.
        let mut made=false;for i in 0..s*s{if mm[i]{mm[i]=false;let k=null(&mm,s);
            if k<b{repairs+=1;b=k;made=true;break}mm[i]=true}}
        assert!(made)
    }
    println!("{} {y} {x} {deleted} {} {repairs} {}",c,best.4,total-deleted-repairs);
    for row in mm.chunks(s){println!("{}",row.iter().map(|&v|if v{'#'}else{'.'}).collect::<String>())}
}
