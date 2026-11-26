"""Extend a patch law by the four bounded-face parent choices of a tree cotree."""
from functools import lru_cache
from itertools import product
from collections import defaultdict
from .odd_charge_parity import build,possible

# Direction of each of the four choices is measured on the dual grid.
edges=[(r,c) for r in range(3) for c in range(2)]+[(r,c) for r in range(2) for c in range(3)]
ends=[(3*r+c,3*r+c+1) for r,c in edges[:6]]+[(3*r+c,3*r+c+3) for r,c in edges[6:]]
face=[(6+r*3+c+1,(r+1)*2+c,6+r*3+c,r*2+c) for r,c in product(range(2),repeat=2)]
@lru_cache(None)
def choices(mask,wall):
    marked=lambda x:mask>>x&1
    taken=[marked(u) or marked(v) for u,v in ends]
    touch=[bool(marked(i)) for i in range(9)]
    for (u,v),yes in zip(ends,taken):
        if yes:touch[u]=touch[v]=True
    # A free edge whose endpoints already touch forced edges cannot be
    # assigned to either primal endpoint. If all neighboring bounded faces
    # are present, one of them must own this edge.
    req=0
    for z,(u,v) in enumerate(ends):
        if taken[z] or not (touch[u] and touch[v]):continue
        interior=z in (2,3,7,10)
        bound=(z in (0,1) and wall&1 or z in (4,5) and wall&2 or
               z in (6,9) and wall&4 or z in (8,11) and wall&8)
        if interior or bound:req|=1<<z
    out=[]
    for ds in product(*[[d for d,z in enumerate(f) if not taken[z]] for f in face]):
        used=sum(1<<z for z in set(face[i][d] for i,d in enumerate(ds)))
        if used.bit_count()!=4 or req&~used:continue
        if not touch[4] and all(used>>z&1 for z in (2,3,7,10)):continue
        out.append(ds)
    return out

def extend(n,cols,qs,rd,mass,labels,take):
    before=len(cols);groups=defaultdict(list);depth=6
    from sys import argv
    depth=int(next((s[2:] for s in argv if s.startswith('d=')),depth))-1
    last=2*depth+6-1
    for i,((t,r,c),m) in enumerate(labels[:before]):
        if t!=1 or not take[i]:continue
        k=t,r,c;wall=int(r==0)+2*int(r==last)+4*int(c==0)+8*int(c==last)
        rid=rd.setdefault(('link','tile',k,m),len(rd));cols[i].append(rid)
        for ds in choices(m,wall):
            j=len(cols);cols.append([~rid]);qs.append(0);take.append(True);labels.append(((2,r,c),(m,ds)));groups[k].append((m,ds,j))
    S=n-2
    ax=lambda j:j if j<depth else 2*depth+6+j-S if j>=S-depth else depth+(j-depth)%6
    for a,b in ((0,1),(1,0)):
        parent={};vertices=set()
        def root(x):
            while x in parent:x=parent[x]
            return x
        for r,c in product(range(S-a),range(S-b)):
            u=0,(1,ax(r),ax(c));v=1,(1,ax(r+a),ax(c+b));vertices.update((u,v));u,v=root(u),root(v)
            if u!=v:parent[max(u,v)]=min(u,v)
        for side,k in sorted(vertices):
            g=root((side,k))
            for m,ds,j in groups[k]:
                bits=tuple(m>>(3*(r-side*a)+c-side*b)&1 for r,c in product(range(a,3),range(b,3)))
                arrows=tuple(ds[2*(r-side*a)+c-side*b] for r,c in product(range(a,2),range(b,2)))
                z=rd.setdefault(('link','dual face',a,b,g,bits,arrows),len(rd))
                cols[j].append(~z if side else z)
    return before
