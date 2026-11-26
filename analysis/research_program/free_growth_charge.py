"""Move an exceptional one-gap optimum to the next side, erasing its NW tooth."""
from itertools import product
from collections import defaultdict,Counter
from .free_perimeter_frame import solve
from .defect_window import table,DIR

def test(n,a,b,d,TAB=None,detail=False,recover=False):
    N=n+3;T,P,S=TAB or table(N)
    val,X=solve(n,3,a,b,False,True)
    assert val==6*n-3
    old=lambda u:(u[0]-a,u[1]-b)
    level=lambda u:min(*old(u),n-1-old(u)[0],n-1-old(u)[1])
    outer={u for u in product(range(N),repeat=2) if level(u)<1}
    rim={u for u in product(range(N),repeat=2) if level(u)==1}
    known={u:int(u in X) for u in outer|rim}
    for i,j in product((2,n-3),repeat=2):known[a+i,b+j]=0
    for i,j in ((2,2),(3,2),(2,3),(2,d)):
        for di,dj in ((0,0),*DIR):known[a+i+di,b+j+dj]=0
    G=defaultdict(list)
    for i,j in outer|rim:
        for h,(di,dj) in enumerate(DIR):
            v=i+di,j+dj
            if v in known and level(v)<=1:
                if (i,j) in X or v in X:G[i,j].append((v,h))
    corners=set(product((0,N-1),repeat=2))
    parents={};sinks=0
    for root in [*sorted(corners),*sorted(X),*sorted(outer)]:
        if root in parents:continue
        sinks+=root in corners;parents[root]=-1;q=[root]
        for u in q:
            for v,h in G[u]:
                if v not in parents:parents[v]=(h+2)%4;q.append(v)
    pc={};sc={};cache={}
    for i,j in {(i-di,j-dj) for i,j in known for di,dj in product(range(3),repeat=2) if 0<=i-di<N-2 and 0<=j-dj<N-2}:
        one=zero=0
        for di,dj in product(range(3),repeat=2):
            z=known.get((i+di,j+dj));h=1<<(3*di+dj)
            if z==1:one|=h
            if z==0:zero|=h
        k=T(1,i,j),one,zero
        if k not in cache:cache[k]=min(q for w,q in enumerate(P(k[0])) if w&one==one and not w&zero)
        if cache[k]:pc[i,j]=cache[k]
    for (i,j),z in known.items():
        ds=tuple(h for h,(di,dj) in enumerate(DIR) if 0<=i+di<N and 0<=j+dj<N)
        nb=[known.get((i+DIR[h][0],j+DIR[h][1])) for h in ds]
        outs=[parents[i,j]] if (i,j) in parents else [-1,*ds]
        q=min(S(T(0,i,j),ds,o,o==-1,False)[z+sum(c<<(j+1) for j,c in enumerate(bs))]
              for bs in product(*[(0,1) if v is None else (v,) for v in nb]) for o in outs)
        if q:sc[i,j]=q
    p=sum(pc.values());s=sum(sc.values());charge=p+s+648*(sinks-1)
    print(n,(a,b),'frame marks',val,'patch',p,'star',s,'corner sinks',sinks,'charge',charge,'budget 936',flush=True)
    if detail:print(pc,sc)
    if recover:return known,parents,pc,sc,936-charge
    return charge
if __name__=='__main__':
    import sys
    n,d=map(int,sys.argv[1:3]);tab=table(n+3)
    for a,b in product((0,3),repeat=2):test(n,a,b,d,tab)
