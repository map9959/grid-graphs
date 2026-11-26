"""Propagate zero-cost physical patches from the two locked diagonals."""
from collections import deque, Counter
from itertools import product
from functools import lru_cache
from .diagonal_score import data,DIR,MASKS
import sys

def run(n,phase,raw=False):
    assert '--deep' in sys.argv and '--three-corners' in sys.argv and n//3%3==1
    k=n//3;pos,P,S,sc,b=data(n,3*k*k+(32*k-7)//6);assert not b
    N=n-2;adj=[];compat=[];domain=[]
    for dx,dy in DIR:
        cells=[3*i+j for i,j in product(range(3),repeat=2) if 0<=i-dx<3 and 0<=j-dy<3]
        def sig(m,z):return sum((m>>(v+z)&1)<<a for a,v in enumerate(cells))
        groups=Counter()
        for m in MASKS:groups[sig(m,-3*dx-dy)]|=1<<m
        compat.append({m:groups[sig(m,0)] for m in MASKS})
    @lru_cache(None)
    def allowed(p,stars):
        ms=[m for m in MASKS if P(p)[m]==0]
        for u,v,z,ds,extra in stars:
            tabs=S(z,ds,extra)
            subset=[(h,3*(u+DIR[d][0])+v+DIR[d][1]) for h,d in enumerate(ds)]
            ms=[m for m in ms if any(tb[(m>>(3*u+v)&1)+2*sum((m>>bit&1)<<h for h,bit in subset)]==0 for tb in tabs.values())]
        return sum(1<<m for m in ms)
    H=next((int(s.split('=')[1]) for s in sys.argv if s.startswith('--height=')),N)
    for i,j in product(range(H),range(N)):
        stars=[]
        for u,v in product(range(3),repeat=2):
            x,y=i+u,j+v;ds=tuple(d for d,(a,c) in enumerate(DIR) if 0<=x+a<n and 0<=y+c<n)
            if all(0<=u+DIR[d][0]<3 and 0<=v+DIR[d][1]<3 for d in ds):
                stars.append((u,v,pos(x,y,0),ds,len(ds)==2 and (x,y)!=(0,0)))
        bits=allowed(pos(i,j,1),tuple(stars))
        if phase>=0 and min(i,j,N-1-i,N-1-j)>=16 and min(abs(i-j),abs(i+j+1-N))<=1:
            bits&=1<<(7<<(3*((phase-i)%3)))
        for u,v in product(range(3),repeat=2):
            if i+u in (0,n-1) and j+v in (0,n-1):
                want=int((i+u,j+v)!=(0,0));bits&=sum(1<<m for m in MASKS if m>>(3*u+v)&1==want)
        domain.append(bits);adj.append([(d,(i+a)*N+j+c) for d,(a,c) in enumerate(DIR) if 0<=i+a<H and 0<=j+c<N])
    @lru_cache(None)
    def union(b,d):
        s=0
        while b:
            l=b&-b;s|=compat[d][l.bit_length()-1];b-=l
        return s
    if raw:return N,domain,union
    q=deque(range(H*N));queued=set(q)
    while q:
        u=q.popleft();queued.remove(u)
        if not domain[u]:print('contradiction at',divmod(u,N));return
        for d,v in adj[u]:
            new=domain[v]&union(domain[u],d)
            if domain[v]!=new:
                domain[v]=new
                if v not in queued:q.append(v);queued.add(v)
    print('side',n,'phase',phase,'singleton patches',sum(b.bit_count()==1 for b in domain),'of',N*N)
    for i in [0,1,2,3,6,12,18,N//2]:
        print(i,''.join('#' if b.bit_count()==1 else '+' if b.bit_count()<6 else '.' for b in domain[N*i:N*i+N]))
    if '--words' in sys.argv:
        for i in range(H):
            row=''
            for j in range(n):
                u,v=min(i,N-1),min(j,N-1);h=3*(i-u)+j-v;b=domain[N*u+v]
                ones=sum(1<<m for m in MASKS if m>>h&1)
                row+=('#' if not b&~ones else '.' if not b&ones else '?')
            print(row)
    return domain
if __name__=='__main__':run(*map(int,sys.argv[1:3]))
