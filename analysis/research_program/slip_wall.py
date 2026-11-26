"""Surface energy at a stationary vertical phase mismatch beside a free side."""
from functools import lru_cache
from .arm_budget_bands import advance

def rate(w):
    # Columns 0..w-1 variable, column w empty (teeth), w+1 an entire
    # marked rail. Every mark in column w-1 attaches to that rail.
    init=(-1,tuple(range(w+1)),(0,)*w+(1,))
    @lru_cache(None)
    def arcs(s):
        old=s[0];out=[]
        for m in range(1<<w):
            if old>=0 and m&((old<<1)|(old>>1)):continue
            z=advance(s,m,1<<(w-1),(1<<w)-1)
            if z is not None:out.append((z,m.bit_count()))
        return out
    dp={init:0};seen={}
    for j in range(250):
        nd={}
        for s,z in dp.items():
            for u,t in arcs(s):nd[u]=max(nd.get(u,-1),z+t)
        mx=max(nd.values());p=frozenset((u,v-mx) for u,v in nd.items())
        if p in seen:
            i,c=seen[p];print('variable width',w,'states',len(nd),'period',j-i,'gain',mx-c,'start',i,flush=True);return
        seen[p]=(j,mx);dp=nd
    raise ValueError('no recurrence')
if __name__=='__main__':
    import sys
    for w in map(int,sys.argv[1:]):rate(w)
