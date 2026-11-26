"""Shrink the two-corner obstruction to signed mark literals; no arrow is fixed."""
from itertools import product
import sys
from pysat.solvers import Solver
from .repair_collar_replay import load,domain,best_orientation
from .diagonal_score import data,generate
from .patch_square import trans
from .sector_gap_cover import verify

def test():
    n=103;tab=data(n,3647);sol=load();marks=domain(n,11);strip=domain(n,14)-domain(n,9)
    boxes=[{trans(i,j,n,g) for i,j in product(range(20),repeat=2)} for g in (2,3)]
    N=n+18;K=N//3;later=data(N,3*K*K+(16*K-7)//3)
    for g in (2,3):
        for i,j in product(range(20),repeat=2):
            for p in (0,1):
                assert tab[0](*trans(i,j,n-2*p,g),p)==later[0](*trans(i,j,N-2*p,g),p)
    assert tab[3:5]==later[3:5]
    old=0;signed=set()
    for g,D in zip((2,3),boxes):
        s={v:sol[v] for v in D&marks}
        val=best_orientation(s,tab,strip,True);old+=val
        for v in sorted(s,reverse=True):
            bit=s.pop(v)
            if best_orientation(s,tab,strip,True)<val:s[v]=bit
        assert best_orientation(s,tab,strip,True)>=val
        print('corner',g,'mark literals',len(s),'certified debit',val,flush=True)
        signed.update((y*n+x+1)*(1 if b[0] else -1) for (y,x),b in s.items())
    d=boxes[1]&strip
    f,X=generate(n,3647,d,False,(*tab[:4],tab[4]-old))
    lits=sorted(X[y*n+x]*(1 if sol[y,x][0] else -1) for y,x in marks&d)
    with Solver(name='cadical195',bootstrap_with=f.clauses) as solver:
        assert not solver.solve(assumptions=lits)
        core=sorted(solver.get_core())
        for z in core.copy():
            rest=[v for v in core if v!=z]
            if not solver.solve(assumptions=rest):core=rest
    for z in core:f.append([z])
    assert verify(f,'repair103_sparse_southern_inner')
    signed.update(core)
    print('inner fixed bits',len(core),'combined distinct literals',len(signed),'remaining budget',tab[4]-old)
    for D in boxes:
        for i in sorted({y for y,x in D}):
            row=''.join('#' if n*i+x+1 in signed else '.' if -(n*i+x+1) in signed else '?' for x in sorted({x for y,x in D}))
            print(row)
        print()
if __name__=='__main__':test()
