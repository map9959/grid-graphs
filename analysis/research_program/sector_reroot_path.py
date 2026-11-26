"""Lower charge of the same forced path oriented to its two different ends."""
from functools import lru_cache
from heapq import heappush, heappop
from itertools import combinations
import sys
from .diagonal_score import data, DIR, MASKS, Q

def run(n,target):
    k=n//3;pos,P,S,sc,budget=data(n,3*k*k+(32*k-7)//6)
    def shift(u,d):return (u[0]+DIR[d][0],u[1]+DIR[d][1])
    def inside(u):return all(0<=v<n for v in u)
    end=(0,n-1) if target=='side' else (n-1,n-1)
    @lru_cache(None)
    def loc(u):
        ds=tuple(d for d in range(4) if inside(shift(u,d)))
        # Charge distinct centered patches (only interior path vertices).
        p=pos(u[0]-1,u[1]-1,1) if len(ds)==4 else None
        return pos(*u,0),ds,p
    @lru_cache(None)
    def options(z,ds,p,incoming,prev,here,endpt):
        tabs=S(z,ds,False);ans={}
        valid={}
        if p:
            ch=P(p)
            for m in MASKS:
                h=(m>>4&1)+sum(((m>>(4+3*DIR[d][0]+DIR[d][1]))&1)<<(a+1) for a,d in enumerate(ds))
                valid[h]=min(valid.get(h,ch[m]),ch[m])
        for h in range(1<<len(ds)):
            if any(h>>a&h>>b&1 and (ds[a]-ds[b])%2 for a,b in combinations(range(len(ds)),2)):continue
            mask=2*h+here
            if p and mask not in valid:continue
            if incoming>=0 and (h>>ds.index(incoming)&1!=prev or not(here or prev)):continue
            for d in ([-1] if endpt else ds):
                if d==incoming or (d>=0 and not(here or h>>ds.index(d)&1)):continue
                m=h>>ds.index(d)&1 if d>=0 else -1
                c=tabs[incoming][mask]+tabs[d][mask]+2*valid.get(mask,0)
                ans[d,m]=min(ans.get((d,m),c),c)
        return tuple((d,m,v) for (d,m),v in ans.items())
    q=[];dist={}
    for m in (0,1):
        st=((0,0),-1,-1,m);dist[st]=0;heappush(q,(0,st))
    while q:
        v,st=heappop(q)
        if dist[st]!=v:continue
        u,di,prev,here=st
        if u==end:
            for _,_,c in options(*loc(u),di,prev,here,True):
                key=('done',);dist[key]=min(dist.get(key,v+c),v+c)
        elif v<dist.get(('done',),float('inf')):
            for d,m,c in options(*loc(u),di,prev,here,False):
                y=shift(u,d)
                if y==(0,0):continue
                s=y,(d+2)%4,here,m
                if s not in dist or v+c<dist[s]:dist[s]=v+c;heappush(q,(v+c,s))
    print(n,target,'two-root path debit',Q(dist['done',],sc),'combined budget',Q(2*budget,sc))
if __name__=='__main__':run(int(sys.argv[1]),sys.argv[2])
