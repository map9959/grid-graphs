"""Transient folded-neighbor relations for testing synchronized schedules."""
from .ShortFoldProbe import trial
from collections import defaultdict
from functools import lru_cache

def geometry(n,ry,lx,ex,samples=(168,)):
    # Positions are centers; the Lean map acts on patch origins.
    def fold(p,d,x,period):
        if x<p:return x
        if x<p+d+period:return p+(x-p)%period
        return x-d
    tables=[]
    for v in (-1,0,1):
        T=defaultdict(set)
        for d in samples:
            N=n+d
            def pt(r,c):
                r-=1;c-=1
                a=9*min(max(0,r-ry)//12,d//12)
                return 1+fold(ry,d,r,12),1+fold(ex,d-a,fold(lx,a,c,3),3)
            def row(r):
                ps=[pt(r,c) for c in range(1,N-1)]
                if v==-1:return ps
                if v==0:return list(zip(ps,ps[1:]))
                return [(p,pt(r+1,c+1)) for c,p in enumerate(ps)]
            prev=[]
            for r in range(1,N-1-int(v==1)):
                ls=row(r)
                for a,b in zip(ls,ls[1:]):T[a,0].add(b);T[b,2].add(a)
                for a,b in zip(prev,ls):T[a,1].add(b);T[b,3].add(a)
                prev=ls
        tables.append({k:tuple(s) for k,s in T.items()})
    return tuple((lambda i,d,T=T:T.get((i,d),())) for T in tables)
if __name__=='__main__':
    import sys
    n,q,ry,lx,ex=map(int,sys.argv[1:])
    print(trial(n,n,q,0,0,geometry(n,ry,lx,ex)),flush=True)
