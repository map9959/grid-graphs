"""All-length minimum deficit of horizontal, star-free one-gap tracks.

Use the certified side-119 catalogue, not a larger board or SAT formula.
"""
from collections import defaultdict
from functools import lru_cache
from itertools import product
import gzip,json
from pathlib import Path
from .tile_rooted_track_cost import step

def bounds():
    B={(u,v):words for u,v,words in json.loads(gzip.decompress(
        Path('target/tile_family_3_5_h6.json.gz').read_bytes()))}
    k=39;K=k-1
    def typ(i):return min(i,6) if i<K-6 else 13+i-K
    def loss(w):return 6-sum(m.bit_count() for m in w)
    for axis in (1,2):
        # Only rows >=3: the halo starts at physical row 4 or later.
        for r in (3,4,5,6,*range(K-6,K)):
            rim=16 if r==K-1 else 0
            def teeth(j):return rim,(63 if j in (0,k-1) else rim),rim
            @lru_cache(None)
            def links(j):
                by=defaultdict(list)
                for w in B[typ(r),typ(j)]:
                    if any(min(r+a,j+b,k-1-r-a,k-1-j-b)>=4 and m&16 and m&(40 if axis==1 else 130)
                           for (a,b),m in zip(product(range(2),repeat=2),w)):continue
                    by[w[0],w[2]].append((w[1],w[3]))
                return by
            def advance(st,j):
                nd={};by=links(j)
                for (w,z),c in st.items():
                    for y in by.get(w,()):
                        s=step(z,y,teeth(j+1))
                        if s is not None:
                            key=y,s;v=c+loss(y)
                            if key not in nd or v<nd[key]:nd[key]=v
                return nd
            st={}
            for w in links(0):
                z=step((-1,tuple(range(7))),w,teeth(0))
                if z is not None:st[w,z]=loss(w)
            for j in range(6):st=advance(st,j)
            for _ in range(K-12):st=advance(st,6)
            old=st
            for _ in range(14):st=advance(st,6)
            assert old and old.keys()==st.keys()
            slopes={key:st[key]-v for key,v in old.items()}
            # Keep a cost for each slope separately. A line dominates
            # another on all t>=0 if it wins at zero and has lower slope.
            layers={s:{key:v for key,v in old.items() if slopes[key]==s}
                    for s in set(slopes.values())}
            def move(layers,j):return {s:advance(v,j) for s,v in layers.items()}
            nxt=layers
            for _ in range(14):nxt=move(nxt,6)
            for s,vs in nxt.items():
                for key,b in vs.items():
                    assert s>=slopes[key] and b>=st[key]
            assert all(nxt[slopes[key]][key]==v for key,v in st.items())
            for j in range(K-6,K):layers=move(layers,j)
            lines=sorted((min(v.values()),s) for s,v in layers.items() if v)
            assert lines==[(10 if typ(r)==12 else 5,0),
                           ({11:36,12:42}.get(typ(r),37),14)]
            print(axis,typ(r),len(st),lines)
            links.cache_clear()

if __name__=='__main__':bounds()
