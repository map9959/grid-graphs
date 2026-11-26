"""Check the port map behind the all-size two-gap frame exchange."""
from functools import lru_cache
from itertools import combinations,product
from .odd_frames import frame,rotate
from .square_dual_physical import DIR,trans

@lru_cache(None)
def ports(n,w):
    f=frame(n,w)
    depth=lambda i,j:min(i,j,n-1-i,n-1-j)
    boundary={p for p in f if depth(*p)==0};lab={}
    for p in sorted(boundary):
        if p in lab:continue
        q=[p];lab[p]=p
        for u in q:
            for a,b in DIR:
                v=u[0]+a,u[1]+b
                if v in boundary and v not in lab and (f[u] or f[v]):lab[v]=p;q.append(v)
    # Name each path by the set of side midpoints it contains.
    arcs={z:tuple(h for h in range(4) if lab[trans(0,n//2,n,h)]==z) for z in set(lab.values())}
    assert len(arcs)==2 and all(arcs.values())
    out={}
    for h in range(4):
        for j in range(2,n-2):
            u=trans(2,j,n,h);foot=trans(0,j,n,h)
            out.setdefault(u,[])
            if f[foot]:out[u].append(arcs[lab[foot]])
    for h in range(4):
        corner=trans(2,2,n,h)
        if w[h] in (1,3):
            assert len(out[corner])==2 and len(set(out[corner]))==1
            del out[corner]
        else:assert len(out[corner])==1
    assert all(len(v)==1 for v in out.values())
    return {u:v[0] for u,v in out.items()}

def check(n=35):
    frames=[w for w in product(range(4),repeat=4) if sum(d%2==0 for d in w)==2]
    reps={min(rotate(w,h) for h in range(8)) for w in frames}
    tests=0
    for w in frames:
        p=ports(n,w);gaps=[i for i in range(4) if not w[i]%2]
        special={trans(2,2,n,i) for i in gaps}
        variants=[]
        for d in (0,2):
            target=tuple(d if i in gaps else 1 for i in range(4))
            q=ports(n,target)
            assert set(q)==set(p) and all(p[u]==q[u] for u in p if u not in special)
            assert len({q[u] for u in special})==2
            variants.append(q)
        # Ordinary teeth of one path have identical labels in all variants.
        # Check all endpoint TYPES, including an ordinary endpoint on either arc.
        ordinary={v:u for u,v in p.items() if u not in special}
        for a,b in combinations([*ordinary.values(),*special],2):
            if p[a]==p[b]:continue
            assert any(q[a]!=q[b] for q in variants);tests+=1
    # Reflecting exchanges both open words at once; closed words can
    # always be reset to 1 at the end.
    normal=set()
    for w in frames:
        if len({d for d in w if d%2==0})!=1:continue
        normal.add(min(tuple(1 if d%2 else d for d in rotate(w,h)) for h in range(8)))
    assert normal=={(0,0,1,1),(0,1,0,1)}
    print(n,len(frames),'words;',len(reps),'D4 classes;',tests,'bridge endpoint types checked; normal forms 0011,0101')
if __name__=='__main__':check()
