//! Delete only clauses whose physical coordinates straddle a free insertion.
use std::{fs::{self,File},io::{BufRead,BufReader,BufWriter,Write,Seek,SeekFrom}};
fn main(){
    let a:Vec<_>=std::env::args().collect();assert_eq!(a.len(),7);
    let raw=fs::read(&a[1]).unwrap();
    let pos:Vec<_>=raw.chunks_exact(4).map(|v|u32::from_ne_bytes(v.try_into().unwrap())).collect();
    let cuts:Vec<_>=a[2..5].iter().map(|s|s.parse::<u32>().unwrap()+1).collect();
    let mut f=BufReader::new(File::open(&a[5]).unwrap());let mut out=BufWriter::new(File::create(&a[6]).unwrap());
    writeln!(out,"{:63}","").unwrap();let mut line=String::new();let mut nc=0;
    loop {
        line.clear();if f.read_line(&mut line).unwrap()==0 {break}
        if line.starts_with('p') {assert_eq!(pos.len(),1+line.split_whitespace().nth(2).unwrap().parse::<usize>().unwrap());continue}
        if line.starts_with('c'){continue}
        let(mut y0,mut y1,mut x0,mut x1)=(65536,0,65536,0);
        for s in line.split_whitespace(){
            let t=pos[s.parse::<i32>().unwrap().unsigned_abs() as usize];let (i,j)=(t>>16,t&65535);
            if i>0{y0=y0.min(i);y1=y1.max(i);}if j>0{x0=x0.min(j);x1=x1.max(j);}
        }
        if y0<cuts[0] && cuts[0]<=y1 || cuts[1..].iter().any(|&x|x0<x && x<=x1){continue}
        out.write_all(line.as_bytes()).unwrap();nc+=1;
    }
    out.seek(SeekFrom::Start(0)).unwrap();writeln!(out,"{:<63}",format!("p cnf {} {}",pos.len()-1,nc)).unwrap();
    println!("distinct interiors; {} intact clauses",nc)
}
