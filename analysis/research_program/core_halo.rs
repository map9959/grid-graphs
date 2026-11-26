//! Restrict a full physical CNF to a set of allowed variable IDs.
use std::{fs::{self,File},io::{BufRead,BufReader,BufWriter,Write,Seek,SeekFrom}};
fn main(){
    let a:Vec<_>=std::env::args().collect();assert_eq!(a.len(),5);
    let r=fs::read(&a[1]).unwrap();let k=a[2].parse::<u8>().unwrap();
    let mut fd=BufReader::new(File::open(&a[3]).unwrap());
    let mut out=BufWriter::new(File::create(&a[4]).unwrap());
    writeln!(out,"{:63}","").unwrap();let mut n=0;let mut line=String::new();
    loop {line.clear();if fd.read_line(&mut line).unwrap()==0{break}
        if line.starts_with('p') {assert_eq!(r.len(),line.split_whitespace().nth(2).unwrap().parse::<usize>().unwrap()+1);continue}
        if line.starts_with('c'){continue}
        if line.split_whitespace().all(|s|r[s.parse::<i32>().unwrap().unsigned_abs() as usize]<=k){
            out.write_all(line.as_bytes()).unwrap();n+=1;
        }
    }
    out.seek(SeekFrom::Start(0)).unwrap();writeln!(out,"{:<63}",format!("p cnf {} {}",r.len()-1,n)).unwrap();
    println!("layer {} vars {} clauses {}",k,r[1..].iter().filter(|&&x|x<=k).count(),n);
}
