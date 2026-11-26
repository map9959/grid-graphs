"""Can the four conserved two-tile transitions meet a clean flat side?"""
from itertools import product
from pathlib import Path
import sys,subprocess
from .defect_window import table,window

def test(halo):
    from pysat.solvers import Solver
    n=119;T=table(n)
    tests=((0,(24,73)),(0,(292,48)),(1,(18,7)),(1,(448,144)))
    for d,pair in tests:
        for far in (0,1):
            along=range(40-halo,46+halo)
            normal=range(n-16-halo,n) if far else range(16+halo)
            dom=set(product(normal,along) if not d else product(along,normal))
            def emit(f,bit,flags):
                for i,j in dom:
                    h=min(i,j,n-1-i,n-1-j)
                    if h<2:f.append([bit(i,j) if h==0 else -bit(i,j)])
                for h,m in enumerate(pair):
                    for a,b in product(range(3),repeat=2):
                        ij=((n-16 if far else 13)+a,40+3*h+b) if not d else (40+3*h+a,(n-16 if far else 13)+b)
                        f.append([bit(*ij)*(1 if m>>(3*a+b)&1 else -1)])
                with Solver(name='cadical195',bootstrap_with=f.clauses) as s:ok=s.solve()
                print(pair,'far',far,'clean-side port',ok,flush=True)
                if not ok:
                    stem=Path(f'target/tile_flux_port_{halo}_{d}_{pair[0]}_{far}');fn=stem.with_suffix('.cnf');pr=stem.with_suffix('.drat')
                    f.to_file(str(fn))
                    with stem.with_suffix('.log').open('wb') as o:assert subprocess.run(['target/cadical/build/cadical',str(fn),str(pr)],stdout=o).returncode==20
                    p=subprocess.run(['target/drat-trim/drat-trim',str(fn),str(pr)],check=True,capture_output=True).stdout
                    assert b's VERIFIED' in p;stem.with_suffix('.check').write_bytes(p);print('s VERIFIED')
            window(n,'rim',1,T,want=False,domain=dom,matching=True,emit=emit)
if __name__=='__main__':test(int(sys.argv[1]))
