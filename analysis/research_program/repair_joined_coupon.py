"""Replay the adjacent-side repair coupon at both reference parities."""
from itertools import product
import sys
from fractions import Fraction
from pysat.solvers import Solver
from .diagonal_score import data,generate
from .repair_defect_budget import charge,check_errors,add_errors
from .sector_gap_cover import verify
from .patch_square import trans

def test(n):
    k=n//3;t=3*k*k+(16*k-7)//3;tab=data(n,t);scale=tab[3]
    D=set(product(range(12),range(21,46)))|set(product(range(12,38),range(29,38)))
    D|={(j,i) for i,j in D}
    ds=[{trans(y,x,n,g) for y,x in D} for g in range(4)]
    assert sum(map(len,ds))==len(set.union(*ds))
    # All labels on the second diagonal already saturate and the far end
    # labels stay on the same phase for +18. Verify the actual D4 tuples.
    N=n+18;K=N//3;tab2=data(N,3*K*K+(16*K-7)//3)
    for y,x in D:
        for tag in (0,1):assert tab[0](y,x,tag)==tab2[0](y,x,tag)
    assert tab[4]==tab2[4] and Fraction(tab[4],scale)==Fraction(7,6)
    for strict in (True,False):
        saved=sys.argv[:]
        try:
            sys.argv.append('--bins='+('24' if strict else '16'))
            ix={};f,X=generate(n,t,D,False,(*tab[:4],scale//3-int(strict)),variables=ix)
        finally:sys.argv[:]=saved
        if not strict:add_errors(f,X,n)
        for flip in (0,1):
            sel=[]
            for j in range(30,37):
                u=f.nv+1;sel.append(u)
                site=lambda y,x:X[(n*x+y) if flip else (n*y+x)]
                f.append([-u,-site(3,j)])
                # North: horizontal bar y=3, so the lateral neighbors
                # are above/below the hole. West is its transpose.
                f.append([-u,*[site(3+h,j+i) for i,h in ((0,-2),(0,-1),(0,1),(0,2),(-1,-1),(-1,1),(1,-1),(1,1))]])
            f.append(sel)
        if strict:
            assert verify(f,f'repair{n}_joined_strict_third')
        else:
            with Solver(name='cadical195',bootstrap_with=f.clauses) as s:
                s.conf_budget(30000);assert s.solve_limited() is True
                true={x for x in s.get_model() if x>0}
            res=check_errors(n,lambda y,x:X[n*y+x] in true)
            val,cap=charge(n,D,tab,X,ix,true)
            assert val<=cap and all(z[0]==81 for z in res)
            print(n,'exact feasible local charge',Fraction(val,scale),'of budget',Fraction(cap,scale),flush=True)
if __name__=='__main__':
    assert '--deep' in sys.argv and not any(z.startswith('--bins=') for z in sys.argv)
    for n in (103,112):test(n)
