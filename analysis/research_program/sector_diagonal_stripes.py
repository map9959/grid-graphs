"""DRAT-checked zero-charge stripe rule along the flat part of a diagonal."""
from itertools import product
from pathlib import Path
import sys, subprocess, hashlib
from .diagonal_score import generate,data

STRIPES=(7,56,448,73,146,292)
def run(n):
    assert n in (139,148) and '--deep' in sys.argv
    k=n//3;t=3*k*k+(32*k-7)//6;tables=data(n,t)
    tagged='_three' if '--three-corners' in sys.argv else ''
    if '--four-corners' in sys.argv:tagged+='_four'
    cases=[(i,i+h) for i,h in product(range(24,27),range(2))]
    if '--ends' in sys.argv:cases=[(i,i+h) for i,h in product(range(7,19),range(2))]
    if '--center' in sys.argv:
        # Last flat triple plus the finite transition into the central X.
        cases=[(i,i+h) for i in range((n-2)//2-12,(n-2)//2+1) for h in range(2)]
    words=STRIPES
    use_budget='--budget' in sys.argv
    if use_budget:tagged+='_budget'+next((s[7:] for s in sys.argv if s.startswith('--bins=')),'exact')
    if '--central-phase' in sys.argv:
        assert n==148
        cases=[(73,73)];words=(292,448);tagged+='_phase'
    halo=next((int(s.split('=')[1]) for s in sys.argv if s.startswith('--halo=')),5)
    if halo!=5:tagged+=f'_h{halo}'
    if '--first' in sys.argv:cases=cases[:1]
    for i,j in cases:
        dom=set(product(range(i-halo,i+3+halo),range(j-halo,j+3+halo)))
        f,X=generate(n,t,dom,not use_budget,tables)
        bits=[X[(i+a)*n+j+b] for a,b in product(range(3),repeat=2)]
        for m in words:f.append([-v if m>>b&1 else v for b,v in enumerate(bits)])
        p=Path(f'target/sector_diagonal_{n}_{i}_{j}{tagged}.cnf');pr=p.with_suffix('.drat')
        f.to_file(str(p))
        with p.with_suffix('.log').open('w') as fd:s=subprocess.run(['target/cadical/build/cadical','-t','25',str(p),str(pr)],stdout=fd).returncode
        if s==20:
            out=subprocess.run(['target/drat-trim/drat-trim',str(p),str(pr)],capture_output=True,check=True).stdout
            assert b's VERIFIED' in out;p.with_suffix('.check').write_bytes(out)
            print(n,i,j,'s VERIFIED',hashlib.sha256(p.read_bytes()).hexdigest(),flush=True)
        else:print(n,i,j,'nonstripe SAT' if s==10 else 'UNKNOWN',flush=True)
if __name__=='__main__':run(int(sys.argv[1]))
