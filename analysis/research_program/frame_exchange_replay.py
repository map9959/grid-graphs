"""Physical check of the uniform three-layer frame, with a contracted old tree."""
from itertools import product
from .odd_frames import frame
from .grow_charge import audit
from .defect_window import table,DIR

def check(n):
    N=n+3;m=frame(n,(0,1,1,1))
    X={(0,j) for j in range(N) if j!=3}|{(i,0) for i in range(2,N)}|{(2,3),(N-1,2)}
    assert len(X)==2*n+5
    new={(i,j) for i,j in product(range(N),repeat=2) if min(i,j)<3}
    par={};root=(-1,-1);e=0
    def rep(u):
        while u in par:u=par[u]
        return u
    def edge(u,v):
        nonlocal e
        a,b=rep(u),rep(v);assert a!=b;par[a]=b;e+=1
    for i,j in new:
        for d,(di,dj) in enumerate(DIR):
            v=i+di,j+dj
            if v in new:
                if d<2 and ((i,j) in X or v in X):edge((i,j),v)
            elif (v[0]-3,v[1]-3) in m and ((i,j) in X or m[v[0]-3,v[1]-3]):
                edge((i,j),root)
    k=(n-2)//3;upper=lambda k:3*k*k+7*k-(k-5)//7
    assert upper(k+1)-upper(k)==len(X)
    print(n,'->',N,'added marks',len(X),'contracted edges',e,'cycle rank 0')
if __name__=='__main__':
    for n in (35,77,119,161,203,245):check(n)
    n=245;t=table(n+3);m=frame(n,(0,1,1,1))
    for d in range(5,192,6):
        p,s,c=audit(n,t,m,3,3,d);assert (p,s,c)==(108,828,1)
    print('245 -> 248, 32 star distances; growth budget 108 patch + 828 star = 936')
