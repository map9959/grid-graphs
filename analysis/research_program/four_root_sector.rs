//! Stream four copies of the exact matching score model; identify physical
//! marks and the bounded-face arrows of the common exterior-rooted cotree.
use std::io::{self, BufRead, Write};
use std::fs::File;
const N:i32=109;
const BASE:i32=644884;
const FACE:i32=BASE-4*(N-1)*(N-1)+1;
fn rot(mut i:i32,mut j:i32,n:i32,g:i32)->(i32,i32){
    for _ in 0..g {(i,j)=(j,n-1-i);}
    (i,j)
}
fn image(v:i32,g:i32)->i32{
    if v<=N*N {
        let (i,j)=rot((v-1)/N,(v-1)%N,N,g);
        return 1+i*N+j
    }
    if v>=FACE {
        let a=(v-FACE)/4;let d=(v-FACE)%4;
        let(i,j)=rot(a/(N-1),a%(N-1),N-1,g);
        return FACE+4*(i*(N-1)+j)+(d+g)%4
    }
    v+g*BASE
}
fn main()->io::Result<()>{
    let mut out=io::BufWriter::new(io::stdout().lock());
    writeln!(out,"p cnf {} {}",3*BASE+FACE-1,4*4370519)?;
    for g in 0..4{
        let mut rd=io::BufReader::new(File::open("target/sector109_4078_matching.cnf")?);
        let mut line=String::new();rd.read_line(&mut line)?;
        assert_eq!(line.trim(),"p cnf 644884 4370519");
        let mut count=0;
        loop{line.clear();if rd.read_line(&mut line)?==0{break}
            for x in line.split_ascii_whitespace(){
                let z:i32=x.parse().unwrap();
                if z==0 {writeln!(out,"0")?;}else{write!(out,"{} ",z.signum()*image(z.abs(),g))?;}
            }
            count+=1;
        }
        assert_eq!(count,4370519);
    }
    Ok(())
}
