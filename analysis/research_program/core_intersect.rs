//! Exact DIMACS clause intersection. Both inputs may contain duplicate clauses.
use std::{collections::HashSet,fs::File,io::{BufRead,BufReader,BufWriter,Write}};
fn main() {
    let a:Vec<_>=std::env::args().collect();assert_eq!(a.len(),4);
    let mut want=HashSet::new(); let mut result=Vec::new();
    let mut nv=0;
    for (pass,path) in a[1..3].iter().enumerate(){
        let mut fd=BufReader::new(File::open(path).unwrap());let mut line=String::new();let mut c=Vec::new();
        loop {
            line.clear(); if fd.read_line(&mut line).unwrap()==0 {break}
            if line.starts_with('p'){nv=line.split_whitespace().nth(2).unwrap().parse::<i32>().unwrap();continue}
            if line.starts_with('c'){continue}
            c.clear();for s in line.split_whitespace(){let z=s.parse::<i32>().unwrap();if z!=0{c.push(z)}}
            c.sort_unstable();
            if pass==0{want.insert(c.clone());}else if want.remove(&c){result.push(c.clone());}
        }
    }
    println!("kept {} exact target clauses; rejected {}",result.len(),want.len());
    let mut out=BufWriter::new(File::create(&a[3]).unwrap());writeln!(out,"p cnf {} {}",nv,result.len()).unwrap();
    for c in result{for z in c{write!(out,"{} ",z).unwrap();}writeln!(out,"0").unwrap();}
}
