"""Periodic transverse interfaces for a bulk block with missing arms."""
from collections import defaultdict
from functools import lru_cache
from .western_cut_transfer import north_star_union,typ
from .neighbor_strip_pump import cols

@lru_cache(maxsize=120000)
def column(z,m,teeth):
    old,part,flags=z;h=len(part)-1;p=list(part)+list(range(h+1,2*h+1))
    data=list(flags)+[(m>>i)&1 for i in range(h)]
    def rt(v):
        while p[v]!=v:v=p[v]
        return v
    def edge(i,j):
        a,b=rt(i),rt(j)
        if a==b:return False
        p[a]=b;data[b]|=data[a];return True
    for i in range(h):
        a=h+1+i;b=h+1+(i+1)%h
        if m&((1<<i)|(1<<((i+1)%h))) and not edge(a,b):return
        if old>=0 and (old|m)>>i&1 and not edge(i,a):return
        if teeth and m>>i&1 and not edge(a,h):return
    roots=[rt(x) for x in (*range(h+1,2*h+1),h)]
    if any(data[i] and p[i]==i and i not in roots for i in range(h)):return
    ids={};pp=tuple(ids.setdefault(v,i) for i,v in enumerate(roots))
    return m,pp,tuple(data[v] if pp[i]==i else 0 for i,v in enumerate(roots))

def run(axis,H,k=39):
    K=k-1
    @lru_cache(None)
    def links(v,eligible):
        tab=defaultdict(list);out=defaultdict(list)
        for a,b,c,d in north_star_union()[6,v]:
            if any(e and m&16 and m&(130 if axis==1 else 40)
                   for e,m in zip(eligible*2,(a,b,c,d))):continue
            tab[a,b].append((c,d))
        def grow(w,y):
            if len(w)==H:
                if (w[0],y[0]) in tab[w[-1],y[-1]]:out[w].append(y)
                return
            for a,b in tab[w[-1],y[-1]]:grow((*w,a),(*y,b))
        for a,b in list(tab):grow((a,),(b,))
        return out
    def by(j):return links(typ(j,K),tuple(min(x,K-x)>=4 for x in (j,j+1)))
    def step(z,w,j):
        for l,m in enumerate(cols(w)):
            z=column(z,m,j in (0,K) and l==1)
            if z is None:return
        return z
    def loss(w):return 3*H-sum(m.bit_count() for m in w)
    def missing(w,j):
        x=6 if j==0 else 7 if j<13 else 192 if j==K else 448 if j>=k-12 else None
        return sum((x is not None and m!=x)<<i for i,m in enumerate(w))
    start=-1,tuple(range(3*H+1)),(0,)*(3*H+1)
    st={}
    for w in by(0):
        z=step(start,w,0)
        if z is not None:st[w,z,missing(w,0)]=loss(w)
    def move(src,j):
        t=by(j);nd={}
        for (w,z,mask),cost in src.items():
            for y in t[w]:
                s=step(z,y,j+1)
                if s is None:continue
                key=y,s,mask|missing(y,j+1);d=cost+loss(y)
                if key not in nd or d<nd[key]:nd[key]=d
        return nd
    for j in range(K):
        st=move(st,j)
        if j==18:
            # Exact supports for any additional length; no cost cap.
            extra=st
            while extra:
                nd=move(extra,j)
                extra={v:c for v,c in nd.items() if c<st.get(v,float('inf'))}
                st.update(extra)
    minima={}
    for (w,(m,pp,flags),mask),c in st.items():
        if any(b and i!=pp[-1] for i,b in enumerate(flags)):continue
        n=mask.bit_count();minima[n]=min(c,minima.get(n,c))
    print(axis,H,'all lengths >=',k,'number missing : minimum rooted periodic deficit',minima,flush=True)
    return minima
if __name__=='__main__':
    import sys
    run(*map(int,sys.argv[1:]))
