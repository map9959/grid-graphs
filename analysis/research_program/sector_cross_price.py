"""Zero-charge perpendicular sector bands with physically separate side contacts."""
from itertools import product
from pathlib import Path
from .diagonal_score import data,generate
from pysat.solvers import Solver

def separate(f,X,n,dom,terminals):
    # Constant two-bit labels propagate across *every* forced edge.
    width=(len(terminals)-1).bit_length()
    ids={v:f.nv+1+width*i for i,v in enumerate(sorted(dom))}
    for code,v in enumerate(terminals):
        for b in range(width):f.append([(ids[v]+b)*(1 if code>>b&1 else -1)])
    for i,j in dom:
        for u,v in ((i+1,j),(i,j+1)):
            if (u,v) not in dom:continue
            for b in range(width):
                a=ids[i,j]+b;c=ids[u,v]+b
                for m in (X[i*n+j],X[u*n+v]):f.extend([[-m,-a,c],[-m,a,-c]])

def pilot(n,a,b,h,*,proof=False):
    from subprocess import run
    k=n//3;T=3*k*k+(32*k-7)//6
    dom={(i,j) for i,j in product(range(n),repeat=2) if a<=i<a+h or b<=j<b+h}
    f,X=generate(n,T,dom,True,data(n,T))
    terminals=[(0,b+h//2),(n-1,b+h//2),(a+h//2,0),(a+h//2,n-1)]
    separate(f,X,n,dom,terminals)
    with Solver(name='cadical195',bootstrap_with=f.clauses) as s:
        s.conf_budget(30000);v=s.solve_limited()
        print('separate flat-side contacts',n,a,b,h,'SAT',v,flush=True)
    if v is False and proof:
        p=Path('target/sector_cross_price');p.mkdir(exist_ok=True)
        cnf=p/'cross.cnf';pr=p/'cross.drat';f.to_file(str(cnf))
        assert run(['target/cadical/build/cadical',str(cnf),str(pr)],capture_output=True).returncode==20
        assert b's VERIFIED' in run(['target/drat-trim/drat-trim',str(cnf),str(pr)],capture_output=True,check=True).stdout
        print('s VERIFIED');cnf.unlink();pr.unlink()
    return v
if __name__=='__main__':
    import sys
    pilot(*map(int,sys.argv[1:5]),proof='--drat' in sys.argv)
