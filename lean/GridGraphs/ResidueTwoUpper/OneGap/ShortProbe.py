"""Exploratory branch count for local mark/arrow arc consistency."""
import sys
from collections import deque
from functools import lru_cache
from itertools import product

from analysis.research_program.defect_window import table, DIR

def trial(n, q):
    typ, patch, star = table(n)
    k=(n-2)//3
    marks={}
    for r,c in product(range(n),repeat=2):
        d=sorted([min(r,n-1-r),min(c,n-1-c)])
        if d[0]==1: marks[r,c]=0
        if d[0]==0 and (d[1]==0 or d[1]>=3): marks[r,c]=1
    for j in range(k):
        if j<q: marks[2,2+3*j]=1
        else:
            m=64 if j==q else 72
            for a,b in product(range(3),repeat=2): marks[1+a,1+3*j+b]=m>>(3*a+b)&1
    ov=[lambda m:m&438,lambda m:m&504,lambda m:(m&219)<<1,lambda m:(m&63)<<3]
    @lru_cache(None)
    def labels(z,d,looking):
        m,o=divmod(z,5)
        active=bool(m&((1<<4)|(1<<[5,7,3,1][d])))
        return 2*ov[d](m)+((active if looking else False)^(o==d))
    @lru_cache(None)
    def outs(A,d,looking): return frozenset(labels(v,d,looking) for v in A)
    @lru_cache(None)
    def narrow(A,d,K): return frozenset(v for v in A if labels(v,d,False) in K)
    @lru_cache(None)
    def domain(pp,ss,ds,bits,paid):
        ts=[star(ss,ds,o,o==-1,len(ds)==2) for o in (*range(4),-1)]
        out=[]
        for m in range(512):
            if pp and patch(pp)[m] or any(v!=-1 and m>>i&1!=v for i,v in enumerate(bits)):continue
            nb=((m>>4)&1)+sum((m>>[5,7,3,1][d]&1)<<(1+i) for i,d in enumerate(ds))
            for o,t in enumerate(ts):
                if t[nb]==72*paid:out.append(5*m+o)
        return frozenset(out)
    V=[(r,c) for r in range(n) for c in range(n)]
    G=[domain(typ(1,r-1,c-1) if 0<r<n-1 and 0<c<n-1 else None,typ(0,r,c),
        tuple(d for d,(a,b) in enumerate(DIR) if 0<=r+a<n and 0<=c+b<n),
        tuple(marks.get((r+a,c+b),-1) if 0<=r+a<n and 0<=c+b<n else 0
              for a,b in product(range(-1,2),repeat=2)),(r,c)==(2,2+3*q)) for r,c in V]
    for j,(r,c) in enumerate(V):
        if 1<=r<n-1 and 1<=c<n-1:
            G[j]=frozenset(z for z in G[j] if all((z%5==d)==bool((z//5)&((1<<4)|(1<<[5,7,3,1][d])))
                for d,(a,b) in enumerate(DIR) if min(r+a,c+b,n-1-r-a,n-1-c-b)==0))
    edges=[[(d,n*(r+a)+c+b) for d,(a,b) in enumerate(DIR)
           if 1<=r+a<n-1 and 1<=c+b<n-1 and 1<=r<n-1 and 1<=c<n-1] for r,c in V]
    @lru_cache(12000)
    def pair(A,B,d):
        e=(d+2)%4
        idx={}
        for b in B:idx.setdefault(labels(b,e,False),[]).append(b)
        return frozenset((a,b) for a in A for b in idx.get(labels(a,d,True),()))
    @lru_cache(24000)
    def flat(A,k):return frozenset(v[k] for v in A)
    @lru_cache(24000)
    def fpush(A,k,K):return frozenset(v for v in A if v[k] in K)
    @lru_cache(24000)
    def padd(A,B,d):
        e=(d+2)%4
        K={(labels(a,e,False),labels(b,e,False)) for a,b in B}
        return frozenset((a,b) for a,b in A if (labels(a,d,True),labels(b,d,True)) in K)
    def pairs(g,d):
        stride=[1,n][d];vstep=[n,1][d];ve=1-d; h=n-2
        A={i:pair(g[i],g[i+stride],d) for i,(r,c) in enumerate(V) if 1<=r<n-1-d and 1<=c<n-2+d}
        todo=deque(A)
        while todo:
            i=todo.popleft();src=A[i]
            if not src:return False
            for dest,back in ((i-stride,True),(i+stride,False),(i-vstep,True),(i+vstep,False)):
                if dest not in A:continue
                B=A[dest]
                if abs(i-dest)==stride:new=fpush(B,int(back),flat(src,int(not back)))
                else:new=padd(B,src,ve if back else 2+ve)
                if new!=B:A[dest]=new;todo.append(dest)
        for i,Z in A.items():
            g[i]=g[i]&flat(Z,0);g[i+stride]=g[i+stride]&flat(Z,1)
        return True
    count=0
    def go(g,work):
        nonlocal count
        count+=1
        if count%10000==0:print('branches',count,flush=True)
        if count>40000:return False
        work=deque(work)
        while work:
            p=work.popleft(); A=g[p]
            for d,v in edges[p]:
                e=(d+2)%4;old=g[v]; new=narrow(old,e,outs(A,d,True))
                if not new:return True
                if old!=new:g[v]=new;work.append(v)
        if 'pairs' in sys.argv:
            for _ in range(12):
                size=sum(map(len,g))
                if not pairs(g,0) or not pairs(g,1):return True
                if sum(map(len,g))==size:break
            if 'nobranch' in sys.argv:return False
        # Split on a mark; direction-only ambiguity need not be explored first.
        candidates=[]
        for j,A in enumerate(g):
            if len(A)<2 or not edges[j]:continue
            for b in (4,):
                yes=frozenset(z for z in A if (z//5)>>b&1)
                if yes and yes!=A:candidates.append((len(A),abs(len(A)-2*len(yes)),j,yes))
        if not candidates:
            a,j=min(((len(a),j) for j,a in enumerate(g) if len(a)>1),default=(0,0))
            if not a:return False
            yes={next(iter(g[j]))}
        else:_,_,j,yes=min(candidates)
        for A in (yes,g[j]-yes):
            gg=g.copy();gg[j]=frozenset(A)
            if not go(gg,[j]):return False
        return True
    print(n,q,go(G,range(n*n)),count,flush=True)
if __name__=='__main__':trial(*map(int,sys.argv[1:3]))
