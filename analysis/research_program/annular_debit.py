"""Minimum grown-board sector charges forced by an opened-and-restored ring."""
from itertools import product
from collections import defaultdict
from .defect_window import DIR

def price(n,N,a,b,ann,X,tab,star=None):
    typ,P,S=tab
    lo,hi=a+1,a+n-2;le,ri=b+1,b+n-2
    rim={(i,j) for i in range(lo,hi+1) for j in (le,ri)}|{(i,j) for j in range(le,ri+1) for i in (lo,hi)}
    tooth=(lo+1,le+1);M=X|{tooth};V={p:int(p in X) for p in ann};V.update({p:0 for p in rim})
    for p in product((lo+1,hi-1),(le+1,ri-1)):V[p]=int(p==tooth)
    if star is not None:
        for x,y in ((0,0),*DIR):V[a+2+x,b+star+y]=0
    # Include exactly the shell, its immediate inward contacts, and the
    # path connecting the two ports of the NW tooth. Other old inward
    # branches attach at most once. Root shell trees on the shell itself.
    active=ann|rim|{tooth};adj=defaultdict(list)
    for p in active:
        for s,(di,dj) in enumerate(DIR):
            q=p[0]+di,p[1]+dj
            if q in active and (p in M or q in M):adj[p].append((q,s))
    corners=set(product((0,N-1),repeat=2));best=(0,0)
    patches={(i-x,j-y) for i,j in V for x,y in product(range(3),repeat=2) if 0<=i-x<N-2 and 0<=j-y<N-2}
    cache={};pq=0
    for i,j in patches:
        t=typ(1,i,j);z=tuple(V.get((i+x,j+y)) for x,y in product(range(3),repeat=2))
        if (t,z) not in cache:cache[t,z]=min(q for m,q in enumerate(P(t)) if all(v is None or m>>h&1==v for h,v in enumerate(z)))
        pq+=cache[t,z]
    for first in corners:
        dirs={}
        for root in [first,*sorted(corners-{first}),*sorted(X),*sorted(ann)]:
            if root in dirs:continue
            dirs[root]=-1;queue=[root]
            for u in queue:
                for v,s in adj[u]:
                    if v not in dirs:dirs[v]=(s+2)%4;queue.append(v)
        roots=sum(dirs[p]<0 for p in corners);sq=648*(roots-1)
        for (i,j),v in V.items():
            ds=tuple(s for s,(di,dj) in enumerate(DIR) if 0<=i+di<N and 0<=j+dj<N)
            nb=[V.get((i+DIR[s][0],j+DIR[s][1])) for s in ds]
            oo=(dirs[i,j],) if (i,j) in dirs else (-1,*ds)
            sq+=min(S(typ(0,i,j),ds,o,o<0,False)[v+2*sum(x<<h for h,x in enumerate(w))]
                    for o in oo for w in product(*[(0,1) if x is None else (x,) for x in nb]))
        best=max(best,(sq+pq,roots))
    return best
