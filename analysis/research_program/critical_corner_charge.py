"""Local sector prices on two incident arms; no assumptions about the other two."""
from itertools import product
from .sector_gap_cover import data,generate,verify
from .patch_square import trans
from pysat.formula import CNF
from pysat.pb import PBEnc

def window(n,rot,side=22):
    k=n//3;t=3*k*k+(16*k-7)//3
    D={trans(i,j,n,rot) for i,j in product(range(side),repeat=2)}
    bill={};f,X=generate(n,t,D,False,data(n,t),bill=bill)
    def test(a,b,limit):
        q=CNF(from_clauses=f.clauses)
        for turn,(mode,phase) in enumerate((a,b)):
            lo=(585,1,9,73)[mode];hi=(585,509,489,329)[mode]
            for j in range(10,side):
                mask=hi if (j-10)%3==phase else lo
                for d in range(10):
                    # Only prescribe marks. In particular every backing
                    # bit on the normal arm is free.
                    if mask>>d&1:
                        y,x=trans(*((j,d) if turn else (d,j)),n,rot);q.append([X[y*n+x]])
        if limit<48:q.extend(PBEnc.atmost(lits=list(bill),weights=list(bill.values()),bound=limit,top_id=q.nv,encoding=8).clauses)
        return verify(q,f'critical_elbow_{n}_{rot}_{side}_{a}_{b}_{limit}')
    return test

if __name__=='__main__':
    import sys
    n=int(sys.argv[1]);rot=int(sys.argv[2]);b=int(sys.argv[3])
    assert '--bins=48' in sys.argv and '--deep' in sys.argv and n%9==4
    test=window(n,rot)
    if '--bars' in sys.argv:assert test((0,0),(0,0),b)
    elif '--shifted' in sys.argv:
        limits={103:(32,16),112:(35,12)}
        for m in range(1,4):assert test((0,0),(m,rot),limits[n][rot])
    else:
        for m,p in product(range(1,4),range(3)):test((0,0),(m,p),b)
