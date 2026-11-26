"""Necessary local fourth-row capacities for a fixed three-row flow."""
from itertools import product
from .sector_oriented import assign
from .seven_threshold import masks
from .square_dual_physical import SYM

def collect(n,j,s,u,ds,loc,ns,ix,d):
    a,b,_,west=s;c=u[1];first=j==0;last=j==n-1
    p=loc(2,j,n,d+4)
    z=loc(1,j-1,n-2,d+3) if not(first or last) else None
    choices=set()
    for A,B,C,W in product(range(2),repeat=4):
        if first and (A or W) or last and C:continue
        aa=a+8*A;bb=b+8*B;cc=c+8*C
        if W and not(A or B):continue
        if z:
            m=masks(aa,bb,cc,4)[1]
            if m not in SYM:continue
            patch=ix[ns['p',min(zip(z,SYM[m]))]]
        for _,dirs in assign(bb,west+8*W,0 if last else bb|cc,4):
            if dirs[:2]!=ds[:2] or (-1 if dirs[2]==1 else dirs[2])!=ds[2]:continue
            nb=(cc>>2&1 if not last else 9,B,aa>>2&1 if not first else 9,bb>>1&1)
            imgs=[]
            for g,pt in enumerate(p):
                rot=lambda x:((2-x if g&4 else x)+g)%4
                word=[9]*4
                for k,v in enumerate(nb):word[rot(k)]=v
                imgs.append((pt,b>>2&1,tuple(word),rot(dirs[2]) if dirs[2]>=0 else -1))
            star=ix[ns['s',min(imgs)]]
            choices.add((star,patch) if z else (star,))
    return choices

def report(n,fixed,ext):
    # t weights: x0+t*x1+binom(t,2)*x2.  Positive union is constant for t>=2.
    for t in (0,1,2,9):
        weights=(1,t,t*(t-1)//2)
        mass=lambda i:sum(w*v.get(i,0) for w,v in zip(weights,fixed))
        bad=[i for i,choices in ext if mass(i)>0 and not any(all(mass(k)>0 for k in choice) for choice in choices)]
        print('fixed chart + projected arcs, side',n+6*t,'unsupported columns',len(bad),'first',bad[:3],
              'required mass',mass(bad[0]) if bad else 0,flush=True)
        if t==9 and bad:
            opts=dict(ext)[bad[0]]
            cover=sorted({next(k for k in v if not mass(k)) for v in opts})
            print('arc',bad[0],'<= sum of sector columns',cover,'actual RHS',sum(map(mass,cover)),flush=True)

def lift_cuts(fixed,ext):
    cuts=set()
    for t in (0,1,2):
        weights=(1,t,t*(t-1)//2)
        mass=lambda i:sum(w*v.get(i,0) for w,v in zip(weights,fixed))
        for i,opts in ext:
            # Every allowed completion must pay into at least one of
            # these missing events. Pooled event counts dominate the mass
            # of this one arc; ties across individual boards are not used.
            if mass(i)>0 and not any(all(mass(k)>0 for k in v) for v in opts):
                js={next(k for k in v if not mass(k)) for v in sorted(opts)}
                cuts.add((i,tuple(sorted(js))))
    print('valid fourth-row support inequalities',len(cuts),flush=True)
    return sorted(cuts)
