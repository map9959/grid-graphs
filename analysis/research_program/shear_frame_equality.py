"""Equality requires the full outer rail in an optimum three-lane frame."""
from itertools import product
from .crop_frame_rate import canonical


def block(state,word):
    old,part=state
    part=part+(max(part)+1,)
    for i,m in enumerate(word):
        p=list(range(8))
        def root(x):
            while p[x]!=x:x=p[x]
            return x
        def link(a,b):
            a,b=root(a),root(b)
            if a==b:return False
            p[b]=a;return True
        for j in range(4):
            if part.index(part[j])!=j:assert link(j,part.index(part[j]))
        for j in range(3):
            if (m|old)&(1<<j) and not link(j,4+j):return
            if j and m&(3<<(j-1)) and not link(4+j,3+j):return
        if (i==1 or m&1) and not link(4,3):return
        part=canonical(root(x) for x in (4,5,6,3))
        old=m
    return old,canonical(part[:3])


def check():
    states=[(0,(0,1,2))];seen=set(states);edges=[]
    for u in states:
        for ms in product(range(8),repeat=3):
            v=block(u,ms)
            if v is not None:
                edges.append((u,v,ms,sum(m.bit_count() for m in ms)-4))
                if v not in seen:seen.add(v);states.append(v)
    pot=dict.fromkeys(states,0)
    for _ in states:
        for u,v,ms,w in edges:pot[v]=max(pot[v],pot[u]+w)
    assert all(w<=pot[v]-pot[u] for u,v,ms,w in edges)
    eq=[(u,v,ms) for u,v,ms,w in edges if w==pot[v]-pot[u]]
    reach={u:{u} for u in states}
    for _ in states:
        for u,v,ms in eq:reach[u].update(reach[v])
    masks={ms for u,v,ms in eq if u in reach[v]}
    print("frame states",len(states),"edges",len(edges),"masks on equality cycles",masks)
    assert masks=={(4,5,4)}


if __name__=='__main__':check()
