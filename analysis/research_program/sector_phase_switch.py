"""Can a diagonal charge window join two distinct absolute pure phases?"""
from itertools import product
from pathlib import Path
import subprocess,sys
from .sector_diagonal_stripes import STRIPES
from .diagonal_score import generate

def run(n,i,j,L,halo):
    k=n//3;dom=set(product(range(i-halo,i+L+3+halo),range(j-halo,j+L+3+halo)))
    f,X=generate(n,3*k*k+(32*k-7)//6,dom)
    labels=[]
    for a in (0,L):
        bits=[X[(i+a+r)*n+j+a+c] for r,c in product(range(3),repeat=2)]
        ids=[f.nv+h for h in range(1,7)]
        f.append(ids);d={}
        for m,z in zip(STRIPES,ids):
            for h,v in enumerate(bits):f.append([-z,v*(1 if m>>h&1 else -1)])
            if m in (7,56,448):key=(0,(i+a+(7,56,448).index(m))%3)
            else:key=(1,(j+a+(73,146,292).index(m))%3)
            d[key]=z
        labels.append(d)
    for key,z in labels[0].items():f.append([-z,-labels[1][key]])
    stem=Path(f'target/sector_switch_{n}_{i}_{j}_{L}_{halo}'+('_four' if '--four-corners' in sys.argv else '')+next(('_bins'+s[7:] for s in sys.argv if s.startswith('--bins=')),''))
    fn=stem.with_suffix('.cnf');pr=stem.with_suffix('.drat');f.to_file(str(fn))
    with stem.with_suffix('.log').open('w') as out:s=subprocess.run(['target/cadical/build/cadical','-t','60',str(fn),str(pr)],stdout=out).returncode
    if s==20:
        out=subprocess.run(['target/drat-trim/drat-trim',str(fn),str(pr)],check=True,capture_output=True).stdout
        assert b's VERIFIED' in out;stem.with_suffix('.check').write_bytes(out);print('UNSAT s VERIFIED')
    else:print('local phase switch SAT' if s==10 else 'UNKNOWN')
if __name__=='__main__':run(*map(int,sys.argv[1:6]))
