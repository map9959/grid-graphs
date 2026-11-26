"""Independent diagnostic for a horizontal pair scan on folded rectangles.

Vertices with the same fold label do not share a mark, direction, or
chosen neighbor. A deletion checks the union over the possible
predecessors/successors in each of the four directions.
"""
from functools import lru_cache
from itertools import product
from collections import deque
from .ShortProbe import DIR, table

def trial(h,w,q,gx,gy,geometry=None):
    typ,patch,star=table(35)
    ax=lambda n,i:i if i<7 else i-(n-35) if i>=n-9 else 7+(i-7)%3
    marks={}
    for r,c in product(range(h),range(w)):
        a=min(r,h-1-r);b=min(c,w-1-c)
        if min(a,b)==1: marks[r,c]=0
        if min(a,b)==0 and max(a,b)>=3: marks[r,c]=1
    for j in range((w-2)//3):
        if j<q:marks[2,2+3*j]=1
        else:
            m=64 if j==q else 72
            for a,b in product(range(3),repeat=2):marks[1+a,1+3*j+b]=m>>(3*a+b)&1
    @lru_cache(None)
    def dom(r,c,fix,wd,iso):
        if iso:return frozenset([64*5+4])
        st=[star(typ(0,r+1,c+1),tuple(range(4)),o,o==-1,False) for o in (0,1,2,3,-1)]
        z=[]
        for m,p in enumerate(patch(typ(1,r,c))):
            if p or any(b!=-1 and (m>>i&1)!=b for i,b in enumerate(fix)):continue
            nb=(m>>4&1)+sum((m>>i&1)<<(d+1) for d,i in enumerate((5,7,3,1)))
            for o,t in enumerate(st):
                if t[nb] or any((o==d)!=bool((m&16) or m&(1<<(5,7,3,1)[d])) for d in wd):continue
                z.append(5*m+o)
        return frozenset(z)
    X={(r,c):dom(ax(h,r-1),ax(w,c-1),tuple(marks.get((r+a,c+b),-1)
              for a,b in product((-1,0,1),repeat=2)),
              tuple(d for d,(a,b) in enumerate(DIR) if min(r+a,c+b,h-1-r-a,w-1-c-b)==0),
              (r,c)==(2,2+3*q))
        for r in range(1,h-1) for c in range(1,w-1)}
    def adj(x,L,g,d):
        a=x+d
        if not 1<=a<L-1:return ()
        if g and x==(g+2 if d==1 else g):return (a,x-2*d)
        return (a,)
    def nbr(k,d):
        r,c=k
        if d in (0,2):return tuple((r,b) for b in adj(c,w,gx,1 if d==0 else -1))
        return tuple((a,c) for a in adj(r,h,gy,1 if d==1 else -1))
    if geometry: nbr=geometry[0]
    @lru_cache(None)
    def port(z,d,send):
        m,o=divmod(z,5)
        ov=(m&438,m&504,(m&219)<<1,(m&63)<<3)[d]
        return 2*ov+((send and bool(m&(16|1<<(5,7,3,1)[d])))^(o==d))
    @lru_cache(25000)
    def filter1(A,B,d):
        K={port(v,d^2,True) for v in B}
        return frozenset(v for v in A if port(v,d,False) in K)
    def sweep(X,nbr,fil):
        Q=deque(X)
        while Q:
            i=Q.popleft();old=X[i];A=old
            for d in range(4):
                ns=nbr(i,d)
                if ns:
                    B=X[ns[0]]
                    for j in ns[1:]: B=B|X[j]
                    A=fil(A,B,d)
            if not A:return False
            if old!=A:
                X[i]=A
                for d in range(4):Q.extend(nbr(i,d))
        return True
    if not sweep(X,nbr,filter1):return 'single'
    @lru_cache(16000)
    def pair(A,B,d):
        K={}
        for b in B:K.setdefault(port(b,d+2,False),[]).append(b)
        return frozenset((a,b) for a in A for b in K.get(port(a,d,True),()))
    for typedir in [0,1]*3:
        d0=typedir
        A={(k,b):pair(S,X[b],d0) for k,S in X.items() for b in nbr(k,d0)}
        def neighbors(e,d):
            k,b=e
            if d==d0:return tuple((b,t) for t in nbr(b,d))
            if d==d0+2:return tuple((t,k) for t in nbr(k,d))
            return tuple(zip(nbr(k,d),nbr(b,d)))
        if geometry: neighbors=geometry[d0+1]
        @lru_cache(32000)
        def filter2(A,B,d):
            if d%2==d0:
                j=int(d<2);K={z[1-j] for z in B}
                return frozenset(z for z in A if z[j] in K)
            K={(port(a,d^2,True),port(b,d^2,True)) for a,b in B}
            return frozenset((a,b) for a,b in A if (port(a,d,False),port(b,d,False)) in K)
        if not sweep(A,neighbors,filter2):return f'pair{typedir}'
        for k,S in X.items():
            for d,i in [(d0,0),(d0+2,1)]:
                es=[(k,t) if not i else (t,k) for t in nbr(k,d)]
                if es:X[k]=X[k]&{z[i] for e in es for z in A[e]}
        filter2.cache_clear()
    return 'open'

if __name__=='__main__':
    import sys
    print(trial(*map(int,sys.argv[1:])),flush=True)
