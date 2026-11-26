"""Integer charges of one physical corner conditional on its rim gap count."""
from itertools import product
from pysat.solvers import Solver
from pysat.pb import PBEnc
from .sector_gap_cover import data,generate,gaps,verify
from .patch_square import trans

def eight(n):
    k=n//3;t=3*k*k+(16*k-7)//3;tables=data(n,t)
    # Root at a largest corner: either its count is >=6, two are >=2,
    # or the partition of eight is (5,1,1,1).
    singles=4 if n==112 else 5
    for turn,charges in ((0,((6,49),(2,25),(5,49-3*singles))),(1,((2,24),(1,singles)))):
        D={trans(i,j,n,turn) for i,j in product(range(26),repeat=2)}
        bill={};f,X=generate(n,t,D,False,tables,bill=bill)
        edges=[(trans(*a,n,turn),trans(*b,n,turn)) for j in range(22)
               for a,b in (((0,j),(0,j+1)),((j,0),(j+1,0)))]
        from pysat.formula import CNF
        for z,l in charges:
            b=CNF(from_clauses=f.clauses);gaps(b,X,edges,n,z)
            b.extend(PBEnc.atmost(lits=list(bill),weights=list(bill.values()),bound=l-1,top_id=b.nv,encoding=8).clauses)
            if not verify(b,f'price8_{n}_{turn}_{z}_{l}'):return False
    return True

def prices(n,t,tables,turn,cap,g,cert=False):
    D={trans(i,j,n,turn) for i,j in product(range(26),repeat=2)}
    bill={};f,X=generate(n,t,D,False,tables,bill=bill)
    edges=[(trans(*a,n,turn),trans(*b,n,turn)) for j in range(22)
           for a,b in (((0,j),(0,j+1)),((j,0),(j+1,0)))]
    out=[]
    from pysat.formula import CNF
    for z in range(g+1):
        base=CNF(from_clauses=f.clauses)
        if z:gaps(base,X,edges,n,z)
        low=out[-1] if out else 0;hi=cap+1
        while low<hi:
            mid=(low+hi)//2
            cc=PBEnc.atmost(lits=list(bill),weights=list(bill.values()),bound=mid,top_id=base.nv,encoding=8)
            with Solver(name='cadical195',bootstrap_with=base.clauses) as s:
                s.append_formula(cc.clauses);s.conf_budget(12000);v=s.solve_limited()
            if v is False:low=mid+1
            else:hi=mid
        out.append(low)
        if cert and low and (z==0 or low>out[-2]):
            base.extend(PBEnc.atmost(lits=list(bill),weights=list(bill.values()),bound=low-1,top_id=base.nv,encoding=8).clauses)
            assert verify(base,f'price{n}_{g}_{turn}_{z}_{low}')
        print('corner',n,turn,z,low,flush=True)
    return out

def main(n,g,cap,cert):
    k=n//3;t=3*k*k+(16*k-7)//3;tables=data(n,t)
    root=prices(n,t,tables,0,cap,g,cert);other=prices(n,t,tables,1,cap,g,cert)
    # Four separate orientations. The gap counts are shared because
    # rerooting changes no mark. In each orientation NW is the root
    # after a rotation/reflection, so every corner is charged once as root.
    cases=[z for z in product(range(g+1),repeat=4) if sum(z)==g and z==tuple(sorted(z))]
    scores=[max(root[x]+sum(other[a] for j,a in enumerate(z) if j!=i) for i,x in enumerate(z)) for z in cases]
    print('minimum bill',min(scores),'budget',cap,'surviving counts', [z for z,v in zip(cases,scores) if v<=cap])
if __name__=='__main__':
    import sys
    g=int(next(z.split('=')[1] for z in sys.argv if z.startswith('--rim-gaps=')))
    cap=int(next(z.split('=')[1] for z in sys.argv if z.startswith('--bins=')))
    if '--eight' in sys.argv:
        assert (g,cap)==(8,48);print('eight gaps excluded?',eight(int(sys.argv[1])))
    else:main(int(sys.argv[1]),g,cap,'--drat' in sys.argv)
