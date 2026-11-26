"""Finite isolated-star test with common physical edge owners, no stored traces.
The two outer rings are relaxed at all corner ports. An active vertex is
allowed to be a sink anywhere. No turning sheets or cycle cuts are needed.
Solver results here are diagnostics, not Lean certificates.
"""
from functools import lru_cache
from itertools import product,combinations
from .defect_window import DIR,table
from .tight_corner_sat import cover
from pysat.solvers import Solver

def check(n):
    typ,patch,star=table(n)
    site=lambda r,c:n*r+c+1
    arc=lambda r,c,d:n*n+4*(site(r,c)-1)+d+1
    charge=lambda r,c:5*n*n+site(r,c)
    candidates=[(2,j) for j in range(5,n-5,6)]
    @lru_cache(None)
    def bans(q,paid):return cover(tuple(z!=(72 if paid else 0) for z in q))
    with Solver(name='cadical195') as sat:
        def exclude(vs,guard,cs):
            for mask,value in cs:
                sat.add_clause(guard+[(-v if value>>k&1 else v) for k,v in enumerate(vs) if mask>>k&1])
        for r,c in product(range(n),repeat=2):
            x=site(r,c);i=min(r,n-1-r);j=min(c,n-1-c)
            if min(i,j)==1:sat.add_clause([-x])
            if min(i,j)==0 and (max(i,j)==0 or max(i,j)>=3):sat.add_clause([x])
            if r+2<n and c+2<n:
                exclude([site(r+a,c+b) for a,b in product(range(3),repeat=2)],[],bans(patch(typ(1,r,c)),False))
            ds=tuple(d for d,(a,b) in enumerate(DIR) if 0<=r+a<n and 0<=c+b<n)
            ns=[site(r+DIR[d][0],c+DIR[d][1]) for d in ds];ids=[arc(r,c,d) for d in ds]
            for v,w in combinations(ids,2):sat.add_clause([-v,-w])
            for d,y,v in zip(ds,ns,ids):
                if d<2:
                    w=arc(r+DIR[d][0],c+DIR[d][1],(d+2)%4)
                    for clause in ([-v,-w],[-x,v,w],[-y,v,w],[-v,x,y],[-w,x,y]):sat.add_clause(clause)
            for o in (-1,*ds):
                q=star(typ(0,r,c),ds,o,o==-1,len(ds)==2);guard=ids if o==-1 else [-arc(r,c,o)]
                if (r,c) in candidates:
                    for pay in [False,True]:exclude([x,*ns],guard+[(-1 if pay else 1)*charge(r,c)],bans(q,pay))
                else:exclude([x,*ns],guard,bans(q,False))
        # Exactly one charged site; selection is imposed by assumptions.
        for r,c in candidates:
            assert not sat.solve(assumptions=[(1 if j==c else -1)*charge(2,j) for _,j in candidates]),c
            print(n,c,'UNSAT',flush=True)
if __name__=='__main__':
    import sys
    for n in map(int,sys.argv[1:]):check(n)
