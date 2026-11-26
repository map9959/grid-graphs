"""Rim gaps counted from both end stars; fine buckets store sums, not averages."""
from collections import Counter
from itertools import product
from .patch_square import DIR,trans
from .square_current import states

def row(ns,n,d,w,holes=False):
    h=d+4;cs=Counter();seen=set()
    ax=lambda x:x if x<h else 2*h+3+x-n if x>=n-h else h+(x-h)%3
    cl=lambda x:max(-w-5,min(w+5,x))
    for i,j in product(range(n),repeat=2):
        if min(i,j,n-1-i,n-1-j):continue
        ps=[(ax(u),ax(v),cl(u-v),cl(u+v+1-n)) for g in range(8) for u,v in [trans(i,j,n,g)]]
        if ps[0] in seen:continue
        seen.add(ps[0]);ds=[s for s,(a,b) in enumerate(DIR) if 0<=i+a<n and 0<=j+b<n]
        for f,sg in states(ds):
            if f:continue
            out=next((s for s,v in sg.items() if v[2]==(1 if s<2 else -1)),-1)
            nb=tuple(sg[s][int(s<2)] if s in ds else 9 for s in range(4))
            z=sum(nb[s]==0 and min(i+DIR[s][0],j+DIR[s][1],n-1-i-DIR[s][0],n-1-j-DIR[s][1])==0 for s in ds)
            if holes:z=4-len(ds)
            if not z:continue
            opts=[]
            for g,p in enumerate(ps):
                rot=lambda s:((2-s if g&4 else s)+g)%4
                v=[9]*4
                for s in ds:v[rot(s)]=nb[s]
                opts.append((p,0,tuple(v),rot(out) if out>=0 else -1))
            cs[ns['s',min(opts)]]+=z
    return list(cs.items())
