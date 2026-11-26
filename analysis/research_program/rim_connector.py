"""Select one forced interior path with one end on each perimeter component."""
from itertools import combinations
from collections import defaultdict
from .odd_frames import DIR

def install(f,bit,edges,n,frames):
    from pysat.card import CardEnc
    def boundary(u):return min(*u,n-1-u[0],n-1-u[1])==0
    ports=defaultdict(list);chosen={}
    for u,v,d in edges:
        if boundary(u) and boundary(v):continue
        x=f.nv+1;chosen[u,v]=x
        f.append([-x,bit(*u),bit(*v)])
        ports[u].append(x);ports[v].append(x)
    for u,vs in ports.items():
        if boundary(u):assert len(vs)==1;continue
        for a,b,c in combinations(vs,3):f.append([-a,-b,-c])
        for z in vs:f.append([-z]+[v for v in vs if v!=z])
    selectors={}
    for code,marks in frames.items():
        sel=f.nv+1;selectors[code]=sel
        comps=[];remaining={u for u in marks if boundary(u)}
        while remaining:
            u=min(remaining);remaining.remove(u);q=[u]
            for i,j in q:
                for a,b in DIR:
                    v=i+a,j+b
                    if v in remaining and (marks[i,j] or marks[v]):
                        remaining.remove(v);q.append(v)
            comps.append(q)
        assert len(comps)==2
        for comp in comps:
            vs=[x for u in comp for x in ports[u]]
            f.append([-sel]+vs)
            enc=CardEnc.atmost(vs,bound=1,top_id=f.nv)
            for c in enc.clauses:f.append([-sel]+c)
    return selectors,chosen

def reverse_charge(f,bit,selected,n,tables,guard):
    """Enforce the required reverse rooting on internal path vertices.

    A reversal is necessary iff both perimeter components contain corners.
    For a cornerless component all four roots induce the same path direction.
    """
    from .tight_corner_sat import cover
    typ,_,star=tables
    for (u,v),x in selected.items():
        for a,b in ((u,v),(v,u)):
            i,j=a;d=DIR.index((b[0]-i,b[1]-j))
            ds=tuple(e for e,(di,dj) in enumerate(DIR) if 0<=i+di<n and 0<=j+dj<n)
            expected=0 if len(ds)==4 else 72
            vs=[bit(i,j)]+[bit(i+DIR[e][0],j+DIR[e][1]) for e in ds]
            vals=star(typ(0,i,j),ds,d,False,len(ds)==2)
            for mask,z in cover(tuple(val!=expected for val in vals)):
                f.append([-guard,-x]+[-y if z>>h&1 else y for h,y in enumerate(vs) if mask>>h&1])

def replay(model,chosen,marks,n,arrows):
    g=defaultdict(list)
    for (u,v),x in chosen.items():
        if x in model:g[u].append(v);g[v].append(u)
    ends=sorted(u for u in g if len(g[u])==1);assert len(ends)==2
    path=[ends[0]]
    while path[-1]!=ends[1]:
        v,=[v for v in g[path[-1]] if v not in path[-2:]];path.append(v)
    assert len(path)==len(g)
    def comp(z):
        seen={z};q=[z]
        for i,j in q:
            for a,b in DIR:
                v=i+a,j+b
                if v in marks and min(*v,n-1-v[0],n-1-v[1])==0 and (marks[i,j] or marks[v]) and v not in seen:
                    q.append(v);seen.add(v)
        return seen
    first=comp(ends[0]);assert ends[1] not in first
    turns=0;last=None
    for u,v in zip(path,path[1:]):
        dr=DIR.index((v[0]-u[0],v[1]-u[1]))
        if last is not None:
            diff=(dr-last)%4;assert diff!=2;turns+=1 if diff==1 else -1 if diff==3 else 0
        last=dr
        for root,out in arrows:
            if root in first:assert out.get(v)==(dr+2)%4
            else:assert out.get(u)==dr
    # Close the path by the clockwise boundary arc from end to start.
    # Each endpoint adds one right turn and the other arc corners each
    # add one. Total clockwise turning of this simple cycle is four.
    perimeter=[(0,j) for j in range(n-1)]+[(i,n-1) for i in range(n-1)]+[(n-1,j) for j in range(n-1,0,-1)]+[(i,0) for i in range(n-1,0,-1)]
    u,v=map(perimeter.index,ends)
    crossed=sum(0<(k*(n-1)-u)%len(perimeter)<(v-u)%len(perimeter) for k in range(4))
    assert turns==crossed-2
    return ends,len(path)-1,turns,max(min(i,j,n-1-i,n-1-j) for i,j in path)
