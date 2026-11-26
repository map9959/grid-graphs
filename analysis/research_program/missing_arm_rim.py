"""End words of a bulk column block as seen by the perpendicular rooted rims."""
from collections import defaultdict
from functools import lru_cache
from pathlib import Path
import gzip,json
from hashlib import sha256
from .arm_budget_bands import B,advance,transpose
from .neighbor_strip_pump import cols

@lru_cache(None)
def catalogue(v,d,north):
    if not north:return B[12,v]
    base=1+3*(1-v) if v<=3 else None
    ph=None if abs(d)==4 else 1+3*d
    if ph==base:return B[0,v]
    p=Path(f'target/tile_star_catalogues/word_0_{v}_{ph}')
    if v<6 and d!=-4 and d!=4 and v+d<1:return ()
    if v>6 and d!=-4 and d!=4 and d>12-v:return ()
    raw=p.with_suffix('.json.gz').read_bytes()
    a,b,_,h=p.with_suffix('.check').read_text().split()
    assert (a,b,h)==('s','VERIFIED',sha256(raw).hexdigest())
    return list(map(tuple,json.loads(gzip.decompress(raw))))

@lru_cache(None)
def edges(v,d,north):
    t=defaultdict(list)
    for a,b,c,e in catalogue(v,d,north):t[a,c].append((b,e))
    return t

@lru_cache(None)
def put(z,y,at_end,north):
    rim=2 if north else 16
    for b,m in enumerate(cols(y)):
        z=advance(z,m,63 if at_end and b==1 else rim,32 if north else 1)
        if z is None:break
    return z

@lru_cache(None)
def words(H,north,phase=None):
    # d=q-j in tile units, with +/-4 meaning beyond the star halo.
    # At j=0 q>=1, and at j=k-1 q<=k-2. South is always star-free.
    def nxt(v,node):
        w,z,d=node
        for y in edges(v,d,north)[w]:
            s=put(z,y,v==12,north)
            if s is None:continue
            for u in ((3,4) if d==4 else (-4 if d<=-2 else d-1,)):
                yield y,s,u
    st=set()
    for d in ((1,2,3,4) if north else (-4,)):
        for w in edges(0,d,north):
            z=put((-1,tuple(range(7)),(0,)*6+(1,)),w,True,north)
            if z is not None:st.add((w,z,d))
    for v in range(6):st={y for x in st for y in nxt(v,x)}
    todo=list(st)
    for x in todo:
        for y in nxt(6,x):
            if y not in st:st.add(y);todo.append(y)
    layers=[st]
    for v in range(7,13):layers.append({y for x in layers[-1] for y in nxt(v,x)})
    end={x for x in layers[-1] if x[2]<=-1 and 2 not in x[1][2]}
    for v in reversed(range(7,13)):end={x for x in layers[v-7] if any(y in end for y in nxt(v,x))}
    prev=defaultdict(list)
    for x in st:
        for y in nxt(6,x):prev[y].append(x)
    todo=list(end)
    for y in todo:
        for x in prev[y]:
            if x not in end:end.add(x);todo.append(x)
    # All prefix/suffix lengths are free, with the *same* chosen star in
    # the two fringes and the observed central subword of this rim.
    paths={x:{(x[0][0 if north else 1],)} for x in st & end if phase is None or x[2]==phase}
    for _ in range(H-1):
        nd=defaultdict(set)
        for x,ps in paths.items():
            for y in nxt(6,x):
                if y in end and (phase is None or y[2]==phase):
                    m=y[0][0 if north else 1]
                    nd[y].update(p+(m,) for p in ps)
        paths=nd
    return {tuple(map(transpose,p)) for ps in paths.values() for p in ps}
