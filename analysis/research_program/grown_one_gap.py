"""Canonical one-gap decision with the neighboring-side dual imposed on old marks."""
from functools import lru_cache
from itertools import product
from pathlib import Path
import sys
from .grow_charge import audit
from .odd_frames import frame
from .defect_window import table,DIR
from .depth_two_far_quarter import run
from .tight_corner_sat import cover
from .extend_forest_28 import verify

def test(n,lo,hi,seconds,mode=0):
    m=frame(n,(0,1,1,1));N=n+3;tab=table(N);T,P,S=tab
    pts=list(range(lo,hi+1,6));assert 5<=lo<=hi<n-5
    # In the extended board root at the unchanged SE corner. The only
    # interior patch with a positive charge is centered at the old isolate.
    p,q,c,pp,ss=audit(n,tab,m,3,3,lo,True)
    assert p+q==936 and c==1 and pp.pop((1,lo-1))==72
    for d in pts[1:]:
        p,q,c,p2,s2=audit(n,tab,m,3,3,d,True)
        assert p+q==936 and c==1 and p2.pop((1,d-1))==72 and pp==p2 and ss==s2
    if mode==0:dom=set(product(range(n),repeat=2))
    else:
        dom={(i,j) for i,j in product(range(n),repeat=2) if (i<mode and lo-mode<=j<=hi+mode) or min(i,j,n-1-i,n-1-j)<2}
    @lru_cache(None)
    def bad(q,amt):return cover(tuple(v!=amt for v in q))
    def extra(f,bit,flags,arc,sheet):
        for u,v in m.items():
            if u in dom:f.append([bit(*u)*(1 if v else -1)])
        count=0
        def emit(vs,q,amt,guard):
            nonlocal count
            for mask,v in bad(q,amt):
                f.append([*guard,*[(-z if v>>k&1 else z) for k,z in enumerate(vs) if mask>>k&1]]);count+=1
        for i,j in sorted(dom):
            # Outside the two original six-layer strips types coincide.
            if min(i,j)>7:continue
            cell=i,j;sq=[(i+a,j+b) for a,b in product(range(3),repeat=2)]
            if all(v in dom for v in sq):
                q=P(T(1,i+3,j+3));vs=list(map(lambda v:bit(*v),sq));flag=flags.get(('s',i+1,j+1))
                if flag:emit(vs,q,72,[-flag]);emit(vs,q,0,[flag])
                else:emit(vs,q,pp.get(cell,0),[])
            if min(i,j)==0:continue # new neighbors outside old square
            ds=tuple(d for d,(a,b) in enumerate(DIR) if 0<=i+a<n and 0<=j+b<n)
            ns=[(i+DIR[d][0],j+DIR[d][1]) for d in ds]
            if any(v not in dom for v in ns):continue
            vs=[bit(i,j),*[bit(*v) for v in ns]];ar=[arc(i,j,d) for d in ds]
            for d in (-1,*ds):
                q=S(T(0,i+3,j+3),ds,d,(i,j)==(n-1,n-1),len(ds)==2)
                emit(vs,q,ss.get(cell,0),ar if d<0 else [-arc(i,j,d)])
        if not mode:
            from .saturated_tile_phase import axis_clauses
            axis_clauses(f,bit,n)
        print('canonical 0111; grown residual clauses',count,flush=True)
    def replay(w,z,X,out):
        if mode:print('local grown-strip SAT',z);return
        rows=[''.join('#' if (i,j) in X else '.' for j in range(n)) for i in range(n)]
        val=verify(rows);k=(n-2)//3;assert val[0]==val[-1]==3*k*k+7*k-(k-5)//7
        Path(f'target/grown_{n}.tree').write_text('\n'.join(rows));print('physical target',val)
    run(n,lo,hi,seconds,domain=dom,root_site=(n-1,n-1),output=f'target/grown_{n}_{lo}_{hi}_{mode}',
        replay=replay,extra_graph=extra,matching=not mode)
if __name__=='__main__':test(*map(int,sys.argv[1:]))
