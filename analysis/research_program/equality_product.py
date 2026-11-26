"""Synchronize eight-row core and frame equality, then restore physical port partitions."""
from collections import defaultdict,Counter
from functools import lru_cache
from .shear_packets import profiles,run
from .crop_frame_rate import step,canonical
from .modified_crop import solve


def scc(graph):
    """Iterative Kosaraju; return only components admitting a closed walk."""
    vis=set();order=[];rev=defaultdict(set)
    for x,ys in graph.items():
        for y in ys:rev[y].add(x)
    for start in list(graph):
        if start in vis:continue
        stack=[(start,False)]
        while stack:
            x,post=stack.pop()
            if post:order.append(x);continue
            if x in vis:continue
            vis.add(x);stack.append((x,True))
            stack.extend((y,False) for y in graph.get(x,()) if y not in vis)
    vis.clear()
    for x in reversed(order):
        if x in vis:continue
        q=[x];vis.add(x);comp=set()
        while q:
            y=q.pop();comp.add(y)
            for z in rev[y]-vis:vis.add(z);q.append(z)
        if len(comp)>1 or x in graph.get(x,()):yield comp


def frame():
    d=solve(1,blocks=5)[-1];base=d;steps=[]
    for ph in range(3):
        nd={};edges=defaultdict(list)
        for s,v in d.items():
            for m in range(64):
                t=step(False,ph,s,m)
                if t is None:continue
                choices=[(t,0)]
                if ph==2:
                    p=list(t[1]);p[6]=max(p)+1
                    choices.append(((m,canonical(p)),1))
                for y,cut in choices:
                    w=v+m.bit_count()-cut
                    nd[y]=max(nd.get(y,-999),w)
                    edges[s].append((m,cut,y,w))
        steps.append({x:[(m,c,y) for m,c,y,w in es if w==nd[y]] for x,es in edges.items()})
        d=nd
    assert d=={x:v+7 for x,v in base.items()}
    triples=defaultdict(list)
    for x in base:
        for a,_,u in steps[0].get(x,()):
            for b,_,v in steps[1].get(u,()):
                for c,cut,y in steps[2].get(v,()):
                    triples[x].append((cut,(a,b,c),y))
    graph={x:{y for _,_,y in es} for x,es in triples.items()}
    return {x:[e for e in triples[x] if e[2] in cc] for cc in scc(graph) for x in cc}


def prepare():
    ins,joins=run(-2,5,unit=True,critical=True,extract=True)
    masks=defaultdict(list)
    def capture(l,r,g,m):
        if ins.get((l,r))==g:masks[l].append((r,m))
    _,L,R=profiles(-2,5,visit=capture)
    fr=frame()
    print("tight core masks",sum(map(len,masks.values())),"frame states",len(fr),
          "frame words",sum(map(len,fr.values())),flush=True)
    return masks,joins,fr


def tile(mask,word):
    # Contract actual immutable rod stars. Keep B_(j+1) as an interface
    # vertex because it is already contacted by the last bottom frame lane.
    ids={}
    def node(r,c):
        for a in (-1,0,1):
            if abs(c-3*a-1)+max(0,r-(3*a-3))<=1:return "A",a
            if abs(c-3*a)+max(0,3*a+6-r)<=1:return "B",a
        return r,c
    def idx(x):
        return ids.setdefault(x,len(ids))
    raw=set()
    for k in range(24):
        if not mask>>k&1:continue
        r,c=divmod(k,3);r-=2
        for rr,cc in ((r-1,c),(r+1,c),(r,c-1),(r,c+1)):
            if not 0<=cc<3:continue
            if cc==0 and rr>5 or cc==1 and rr< -2:continue
            raw.add(tuple(sorted(((r,c),(rr,cc)))))
    edges=[(idx(node(*a)),idx(node(*b))) for a,b in raw]
    for c,m in enumerate(word):
        for i in range(6):
            u=idx(('F',i,c))
            if i%3 and m&(3<<(i-1)):edges.append((u,idx(('F',i-1,c))))
            if c and (m|word[c-1])&(1<<i):edges.append((u,idx(('F',i,c-1))))
        if c==1 or m&1:edges.append((idx(('F',0,c)),idx(('A',0))))
        if c==0 or m&8:edges.append((idx(('F',3,c)),idx(('B',int(c==2)))))
    left=[idx(('F',i,0)) for i in range(6)]+[idx(node(r,0)) for r in range(-5,6)]+[idx(('B',0))]
    right=[idx(('F',i,2)) for i in range(6)]+[idx(node(r,2)) for r in range(-2,9)]+[idx(('B',1))]
    p=list(range(len(ids)))
    def root(i):
        while p[i]!=i:i=p[i]
        return i
    for a,b in edges:
        a,b=root(a),root(b)
        if a==b:return
        p[a]=b
    lm=word[0]|sum(1<<(i+9) for i in range(8) if mask>>(3*i)&1)
    rm=word[2]|sum(1<<(i+6) for i in range(8) if mask>>(3*i+2)&1)
    return lm,rm,canonical(root(x) for x in left+right)


def physical_input(audit=False):
    ms,j,f=prepare()
    fs=list(f);fx={s:i for i,s in enumerate(fs)}
    ids={};arcs=set();nm=0;examples={}
    @lru_cache(None)
    def get(m,w):
        data=tile(m,w)
        if data is not None:
            i=ids.setdefault(data,len(ids))
            if audit:examples.setdefault(i,(m,w))
            return i
    for l,es in ms.items():
        for r,m in es:
            for x,words in f.items():
                for cut,w,y in words:
                    t=get(m,w)
                    if t is None:continue
                    for nxt,c in j[r]:
                        if cut==c:
                            arcs.add((l*len(f)+fx[x],nxt*len(f)+fx[y],t))
                            nm+=1
    # Eliminate physically cyclic single tiles and nonrecurrent discrete states.
    graph=defaultdict(set)
    for x,y,t in arcs:graph[x].add(y)
    kept={x:i for i,cc in enumerate(scc(graph)) for x in cc}
    reduced=[(x,y,t) for x,y,t in arcs if x in kept and kept[x]==kept.get(y)]
    print("single-tile product: feasible labeled arcs",nm,"distinct arcs",len(arcs),
          "within SCCs",len(reduced),"states",len(kept),"tiles",len({t for x,y,t in reduced}),flush=True)
    direct=crosscheck(list(ids),reduced,examples) if audit else None
    return list(ids),reduced,direct


def crosscheck(tiles,arcs,examples):
    """Independently compare bare-coordinate cycles with component gluing."""
    import random
    rng=random.Random(1418)
    adj=defaultdict(list)
    for x,y,t in sorted(arcs):adj[x].append((y,t))
    def by_ports(ts):
        part=tuple(range(18));mask=0
        for t in ts:
            lm,rm,p=tiles[t]
            comp=[{i} for i in range(54)]
            for i in range(18):
                if i==17 or (mask|lm)>>i&1:
                    a=next(c for c in comp if part[i] in c)
                    b=next(c for c in comp if 18+p[i] in c)
                    if a is b:return False
                    a.update(b);comp.remove(b)
            part=canonical(next(k for k,c in enumerate(comp) if 18+q in c) for q in p[18:])
            mask=rm
        return True
    def by_cells(ts):
        # Include one extra immutable crop column on either side to retain
        # the off-strip rod supports, including B_(last+1). Only the actual
        # packet and frame masks are inserted; no lookup of port labels.
        cols=3*len(ts);h=cols+27;F=set()
        for c in range(-1,cols+1):
            j=c//3
            for y in range(h):
                r=y-12-3*j
                if y<3 or y>=h-3:
                    if 0<=c<cols:
                        m,w=examples[ts[j]]
                        i=2-y if y<3 else 3+y-(h-3)
                        if w[c%3]>>i&1:F.add((y,c))
                elif c%3==1 and r< -2 or c%3==0 and r>5:F.add((y,c))
                elif 0<=c<cols and -2<=r<=5:
                    m,w=examples[ts[j]]
                    if m>>(3*(r+2)+c%3)&1:F.add((y,c))
        p={}
        def root(x):
            while x in p:x=p[x]
            return x
        for y in range(h):
            for c in range(-1,cols+1):
                u=y,c
                for v in ((y+1,c),(y,c+1)):
                    if v[0]>=h or v[1]>cols or not (v in F or u in F):continue
                    a,b=root(u),root(v)
                    if a==b:return False
                    p[a]=b
        return True
    ct=Counter()
    for n in range(1,8):
        for _ in range(96):
            start=rng.choice(sorted(adj));ts=[]
            for _ in range(n):
                start,t=rng.choice(adj[start]);ts.append(t)
            observed=by_cells(ts);assert observed==by_ports(ts),(n,ts,observed)
            ct[n,observed]+=1
    print("physical-coordinate controls (length, forest):",sorted(ct.items()),flush=True)
    return by_cells


def test():
    from pathlib import Path
    import json,subprocess
    tiles,arcs,direct=physical_input(audit=True)
    executable=Path(__file__).resolve().parents[2]/"target/release/equality_product"
    out=subprocess.run([executable],input=json.dumps(dict(tiles=tiles,arcs=arcs)),text=True,
                       capture_output=True,check=True).stdout
    print(out,end='')
    path=next(json.loads(line.split(': ',1)[1]) for line in out.splitlines()
              if line.startswith('longest physical walk:'))
    assert len(path)==5 and direct(path)
    print("longest positive control: five blocks replayed on physical grid, forest")

if __name__=="__main__":test()
