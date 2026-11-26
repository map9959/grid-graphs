"""Residual budget on the three-layer growth of an exceptional one-gap target."""
from itertools import product
from collections import defaultdict
from .perimeter_extension import growth
from .odd_frames import frame
from .defect_window import table,DIR

def audit(n,tab,m,a,b,d,details=False,seed=None):
    N=n+3;T,P,S=tab;score,X=growth(n,3,a,b,m,True,seed);assert score==2*n+5
    V={(i+a,j+b):v for (i,j),v in m.items()};per={u for u in V if min(u[0]-a,u[1]-b,a+n-1-u[0],b+n-1-u[1])==0}
    outer={(i,j) for i,j in product(range(N),repeat=2) if not(a<=i<a+n and b<=j<b+n)}
    V.update({u:int(u in X) for u in outer});shell=outer|per
    for i,j in product((2,n-3),repeat=2):
        V[a+i,b+j]=int(i==j==2)
    star=a+2,b+d
    for x,y in ((0,0),*DIR):V[star[0]+x,star[1]+y]=0
    adj=defaultdict(list)
    for i,j in shell:
        for k,(x,y) in enumerate(DIR):
            u=i+x,j+y
            if u in shell and (V[i,j] or V[u]):adj[i,j].append((u,k))
    par={};corners=set(product((0,N-1),repeat=2))
    # Root component meeting the old perimeter first at the unchanged
    # physical corner. Any other component is completely in the addition.
    oldroot=(a if a==0 else N-1,b if b==0 else N-1)
    roots=[oldroot,*sorted(corners-{oldroot}),*sorted(X),*sorted(shell)]
    for root in roots:
        if root in par:continue
        par[root]=-1;q=[root]
        for u in q:
            for v,k in adj[u]:
                if v not in par:par[v]=(k+2)%4;q.append(v)
    sinks=sum(par[u]<0 for u in corners)
    pq=sq=0;pp={};ss={}
    # Include even partial patches by taking their individually least
    # possible charge. The stencil is nonnegative on all legal masks.
    nearby={ (i-x,j-y) for i,j in V for x,y in product(range(3),repeat=2) if 0<=i-x<N-2 and 0<=j-y<N-2}
    cache={}
    for i,j in nearby:
        ones=zeros=0
        for x,y in product(range(3),repeat=2):
            z=V.get((i+x,j+y))
            if z==1:ones|=1<<(3*x+y)
            elif z==0:zeros|=1<<(3*x+y)
        key=T(1,i,j),ones,zeros
        if key not in cache:cache[key]=min(q for w,q in enumerate(P(key[0])) if w&ones==ones and not w&zeros)
        pq+=cache[key]
        if cache[key]:pp[i-a,j-b]=cache[key]
    for (i,j),v in V.items():
        ds=tuple(h for h,(x,y) in enumerate(DIR) if 0<=i+x<N and 0<=j+y<N)
        ns=[V.get((i+DIR[h][0],j+DIR[h][1])) for h in ds]
        outs=[par[i,j]] if (i,j) in par else [-1,*ds]
        typ=T(0,i,j)
        z=min(S(typ,ds,o,o==-1,False)[v+sum(c<<(j+1) for j,c in enumerate(bts))]
                for bts in product(*[(0,1) if z is None else (z,) for z in ns]) for o in outs)
        sq+=z
        if z:ss[i-a,j-b]=z
    return (pq,sq,sinks,pp,ss) if details else (pq,sq,sinks)
if __name__=='__main__':
    import sys
    n,d=map(int,sys.argv[1:3]);tab=table(n+3)
    for s in product((1,3),repeat=3):
        m=frame(n,(0,*s))
        for a,b in product((0,3),repeat=2):
            p,q,c=audit(n,tab,m,a,b,d)
            print(n,s,a,b,p,q,c,'minimum accounted',p+q+648*(c-1),'budget 936',flush=True)
