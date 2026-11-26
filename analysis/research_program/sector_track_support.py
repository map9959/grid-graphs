"""Test whole transverse strips against the exact four-row optimal moments."""
from collections import defaultdict,Counter
from fractions import Fraction
from functools import lru_cache
from pathlib import Path
from itertools import product
from .patch_square import relaxation,MASKS,SYM,trans
import json,sys

def support(n):
    base=55+(n-55)%6;t=(n-base)//6
    assert t>=0
    ns,_,_=relaxation(43+(n-43)%6,6,pooled=2,period=3,diagonal=2)
    inv={a:i for i,a in enumerate(ns.values())}
    moments=json.loads(Path(__file__).with_name(f'oriented_strip_4_2_2_{base}_flows.json').read_text())
    positive={int(i) for h,vec in enumerate(moments) if (1,t,t*(t-1)//2)[h]>0 for i,z in vec.items() if Fraction(z)>0}
    N=n-2
    def typ(i,j):
        ax=lambda x:x if x<5 else 13+x-N if x>=N-5 else 5+(x-5)%3
        clip=lambda x:max(-7,min(7,x))
        return ax(i),ax(j),clip(i-j),clip(i+j+1-N)
    @lru_cache(None)
    def ms(img):
        return tuple(m for m in MASKS if inv[ns['p',min(zip(img,SYM[m]))]] in positive)
    return [[ms(tuple(typ(*trans(i,j,N,g)) for g in range(8))) for j in range(N)] for i in range(N)]

@lru_cache(None)
def layer(allowed):
    rows=[(m&7,m>>3&7,m>>6) for m in allowed[0]]
    for j,opts in enumerate(allowed[1:],1):
        by=defaultdict(list)
        for m in opts:
            a,b,c=m&7,m>>3&7,m>>6
            by[a&3,b&3,c&3].append((a>>2,b>>2,c>>2))
        rows=[(a|x<<(j+2),b|y<<(j+2),c|z<<(j+2)) for a,b,c in rows for x,y,z in by[a>>j,b>>j,c>>j]]
    return rows

@lru_cache(None)
def advance(H,oldmask,p,top,new):
    parent=list(p)+list(range(H,2*H))
    def root(u):
        while parent[u]!=u:u=parent[u]
        return u
    def edge(x,y):
        a,b=root(x),root(y)
        if a==b:return False
        parent[a]=b;return True
    for j in range(H):
        if (oldmask|new)>>j&1 and not edge(j,j+H):return
        if j and new>>(j-1)&3 and not edge(j-1+H,j+H):return
    roots=[root(j+H) for j in range(H)];touch={root(j) for j in range(H) if top>>j&1}
    return tuple(roots.index(z) for z in roots),sum((z in touch)<<j for j,z in enumerate(roots))

def teststrip(allowed,j,H):
    st=set()
    for i,row in enumerate(allowed):
        choices=layer(tuple(row[j:j+H-2]))
        if i==0:
            for a,b,c in choices:
                # The first row has horizontal forced edges only.
                p=[0]
                for h in range(1,H):p.append(p[-1] if a>>(h-1)&3 else h)
                q=advance(H,a,tuple(p),(1<<H)-1,b)
                if q is None:continue
                z=advance(H,b,*q,c)
                if z is not None:st.add((b,c,*z))
        else:
            by=defaultdict(list)
            for a,b,c in choices:by[a,b].append(c)
            nxt=set()
            for a,b,p,f in st:
                for c in by[a,b]:
                    z=advance(H,b,p,f,c)
                    if z is not None:nxt.add((b,c,*z))
            st=nxt
        if not st:return 'no strip'
    return 'must cross' if all(s[-1] for s in st) else 'no crossing possible or required'

def linear(n):
    assert n%3==1 and n>=67
    a=support(n);r=4 if n%6==1 else 3
    prototype=tuple(a[r][18:21]);assert len(layer(prototype))==0
    starts=list(range(18,n-20,3))
    for j in starts:assert tuple(a[r][j:j+3])==prototype
    assert len(starts)==(n-1)//3-12
    print('side',n,'row',r,'zero admissible 3x5 words;',len(starts),'disjoint triples of origins must each emit an off-support patch')

def run(n,H):
    a=support(n);res=defaultdict(list)
    for j in range(n-H+1):res[teststrip(a,j,H)].append(j)
    for k,vs in res.items():print(n,H,k,len(vs),vs)
if __name__=='__main__':
    if '--linear' in sys.argv:linear(int(sys.argv[1]))
    else:run(*map(int,sys.argv[1:]))
