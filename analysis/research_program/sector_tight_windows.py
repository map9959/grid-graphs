"""Constant 1/6-budget test on disjoint residue-one corner windows, sharing marks across rootings."""
from .diagonal_score import generate
from .patch_square import trans
from pathlib import Path
from itertools import product
import subprocess,sys

def test(n,R,seconds):
    k=(n-1)//3;assert n==3*k+1 and k%3==1 and k>=18 and 2*R+10<n
    rim='--rim' in sys.argv
    depth=min if rim else max
    dom={(i,j) for i,j in product(range(n),repeat=2) if depth(min(i,n-1-i),min(j,n-1-j))<R}
    T=3*k*k+(32*k-7)//6;f,X=generate(n,T,dom,zero='--zero' in sys.argv);old=f.clauses.copy();nv=f.nv
    for g in (1,2,3):
        offset=f.nv;ids=[0]+[offset+z for z in range(1,nv+1)]
        for i,j in dom:
            x,y=trans(i,j,n,g);ids[X[n*i+j]]=X[n*x+y]
        f.extend([[ids[abs(z)]*(1 if z>0 else -1) for z in cl] for cl in old])
    mode=next((s.split('=')[1] for s in sys.argv if s.startswith('--corner=')),'all')
    if mode=='unmarked':f.append([-X[0]])
    if mode=='bare':f.extend([[-X[1]],[-X[n]]])
    if mode=='two':
        from itertools import combinations
        corners=[X[n*i+j] for i,j in product((0,n-1),repeat=2)]
        for triple in combinations(corners,3):f.append([-z for z in triple])
    assert mode in ('all','unmarked','bare','two')
    if '--three-corners' in sys.argv or '--four-corners' in sys.argv:
        for u in (n-1,n*(n-1),n*n-1):f.append([X[u]])
        f.append([X[0] if '--four-corners' in sys.argv else -X[0]])
        for g in range(4):
            u,v=trans(0,1,n,g),trans(1,0,n,g)
            f.append([X[n*u[0]+u[1]],X[n*v[0]+v[1]]])
    phase=next((int(s.split('=')[1]) for s in sys.argv if s.startswith('--phase=')),None)
    if phase is not None:
        for i,j in dom:
            r,c=min(i,n-1-i),min(j,n-1-j)
            if 16<=min(r,c) and abs(r-c)<=1:f.append([X[n*i+j]*(1 if i%3==phase else -1)])
    cheap=next((int(s.split('=')[1]) for s in sys.argv if s.startswith('--cheap=')),None)
    if cheap is not None:
        from pysat.card import CardEnc
        ids=[]
        for i,j in product(range(7,R-2),repeat=2):
            if abs(i-j)>1:continue
            # At most two words differ from the one common stripe on
            # the cheap arm (and these cannot be any other pure phase).
            z=f.nv+1;ids.append(z)
            vs=[X[n*(i+a)+j+b] for a,b in product(range(3),repeat=2)]
            hm=7<<(3*((cheap-i)%3))
            for h,v in enumerate(vs):f.append([z,v*(1 if hm>>h&1 else -1)])
            for m in (7,56,448,73,146,292):
                if m!=hm:f.append([v*(-1 if m>>h&1 else 1) for h,v in enumerate(vs)])
        f.extend(CardEnc.atmost(lits=ids,bound=2,top_id=f.nv).clauses)
    suffix=('' if mode=='all' else '_'+mode)+('_three' if '--three-corners' in sys.argv else '_four' if '--four-corners' in sys.argv else '')+('_zero' if '--zero' in sys.argv else '')+('_rim' if rim else '')+(f'_phase{phase}' if phase is not None else '')+(f'_cheap{cheap}' if cheap is not None else '')
    fn=Path(f'target/sector_tight_windows_{n}_{R}{suffix}.cnf');pr=fn.with_suffix('.drat');f.to_file(str(fn))
    with fn.with_suffix('.log').open('wb') as fd:s=subprocess.run(['target/cadical/build/cadical','-t',str(seconds),str(fn),str(pr)],stdout=fd).returncode
    if s==20:
        proof=subprocess.run(['target/drat-trim/drat-trim',str(fn),str(pr)],check=True,capture_output=True).stdout
        assert b's VERIFIED' in proof;fn.with_suffix('.check').write_bytes(proof);print('UNSAT s VERIFIED',flush=True)
    else:print('joint corner relaxation SAT' if s==10 else 'UNKNOWN',flush=True)
if __name__=='__main__':test(*map(int,sys.argv[1:4]))
