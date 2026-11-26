"""Test zero sector charge on a repeating finite straight or diagonal band."""
import sys, subprocess
from pathlib import Path
from .diagonal_score import generate

def run(n,width,length,kind,timeout):
    k=n//3;T=3*k*k+(32*k-7)//6
    off=width+12
    if kind=='north':
        dom={(r,off+j) for r in range(width) for j in range(length)}
    elif kind=='diagonal':
        dom={(off+j+r,off+j) for r in range(-width,width+1) for j in range(length)}
    else:raise ValueError(kind)
    assert max(max(p) for p in dom)<n-off and (kind!='diagonal' or 2*(off+length+width)+10<n)
    f,_=generate(n,T,dom,zero=True)
    stem=Path(f'target/sector_zero_{n}_{width}_{length}_{kind}'+('_three' if '--three-corners' in sys.argv else ''))
    fn=stem.with_suffix('.cnf');pr=stem.with_suffix('.drat');f.to_file(str(fn))
    with stem.with_suffix('.log').open('wb') as fd:s=subprocess.run(['target/cadical/build/cadical','-t',str(timeout),str(fn),str(pr)],stdout=fd).returncode
    if s==20:
        out=subprocess.run(['target/drat-trim/drat-trim',str(fn),str(pr)],capture_output=True,check=True).stdout
        assert b's VERIFIED' in out;stem.with_suffix('.check').write_bytes(out)
        print('UNSAT s VERIFIED')
    else:print('SAT zero band' if s==10 else 'UNKNOWN')

if __name__=='__main__':run(*map(int,sys.argv[1:4]),sys.argv[4],int(sys.argv[5]))
