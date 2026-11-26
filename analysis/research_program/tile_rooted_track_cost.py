"""Minimum deficit of a six-site-wide track with the real crop roots tied."""
from itertools import product
from collections import defaultdict
from functools import lru_cache
from .tile_family_lp import projected,typ
import sys

@lru_cache(None)
def advance(state,m,teeth):
    # Last column's six sites and virtual common root, then six new sites.
    old,pp=state;p=list(pp)+list(range(7,13))
    def rt(i):
        while p[i]!=i:i=p[i]
        return i
    def edge(u,v):
        a,b=rt(u),rt(v);p[a]=b;return a!=b
    for i in range(6):
        if old>=0 and (old|m)>>i&1 and not edge(i,7+i):return
        if i and m>>(i-1)&3 and not edge(6+i,7+i):return
        if teeth>>i&m>>i&1 and not edge(7+i,6):return
    canon={};ls=[rt(x) for x in (7,8,9,10,11,12,6)]
    return m,tuple(canon.setdefault(v,i) for i,v in enumerate(ls))

@lru_cache(None)
def step(state,pair,teeth):
    for j in range(3):
        m=sum(((pair[h//3]>>(3*(h%3)+j))&1)<<h for h in range(6))
        state=advance(state,m,teeth[j])
        if state is None:return
    return state

def run(n,axis,row,vertical=False):
    k=(n-2)//3;K=k-1;assert 0<=row<K
    pure=next((int(s[7:]) for s in sys.argv if s.startswith('--pure=')),None)
    B=projected(3,5);dom={}
    def transpose(m):return sum((m>>(3*i+j)&1)<<(3*j+i) for i,j in product(range(3),repeat=2))
    for j in range(K):
        u,v=typ(row,K),typ(j,K);p=(u,v)
        if p in dom:continue
        ls=B[p if not vertical else (v,u)];by=defaultdict(list)
        for w in ls:
            if vertical:w=tuple(transpose(w[h]) for h in (0,2,1,3))
            mask=40 if (axis==1)!=vertical else 130
            if any(min(row+a,j+b,k-1-row-a,k-1-j-b)>=4 and z&16 and z&mask for (a,b),z in zip(product(range(2),repeat=2),w)):continue
            if pure is not None and any(min(row+a,j+b,k-1-row-a,k-1-j-b)>=4 and z.bit_count()==3 and z!=pure
                      for (a,b),z in zip(product(range(2),repeat=2),w)):continue
            by[w[0],w[2]].append((w[1],w[3]))
        dom[p]=by
    # The first and last physical columns are at depth one, and empty,
    # so they do not create a path between different crop teeth.
    rim=sum(1<<i for i in range(6) if 1+3*row+i in (2,n-3))
    def teeth(j):return (rim,63 if j in (0,k-1) else rim,rim)
    def loss(pair):return 6-sum(m.bit_count() for m in pair)
    st={};base=-1,tuple(range(7))
    for w in dom[typ(row,K),typ(0,K)]:
        z=step(base,w,teeth(0))
        if z:st[w,z]=loss(w)
    for j in range(K):
        nd={};by=dom[typ(row,K),typ(j,K)]
        for (w,z),cost in st.items():
            for y in by.get(w,()):
                s=step(z,y,teeth(j+1))
                if s is not None:
                    key=y,s;c=cost+loss(y)
                    if c<nd.get(key,10**6):nd[key]=c
        st=nd
    print('side',n,'axis',axis,'track',row,'vertical',vertical,'end states',len(st),'minimum deficit',min(st.values(),default=None))
    return min(st.values(),default=None)
if __name__=='__main__':run(*(int(s) for s in sys.argv[1:] if not s.startswith('--')))
