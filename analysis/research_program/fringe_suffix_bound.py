"""Uniform plateau bounds for an east-grounded 448 suffix near the west."""
import gzip,json
from collections import defaultdict
from pathlib import Path
from .neighbor_diagonal import push

def check(B=None,star_at_near_end=False):
    if B is None:
        B={(u,v):ws for u,v,ws in json.loads(gzip.decompress(
            Path('target/tile_family_3_5_h6.json.gz').read_bytes()))}
    # Moving north in bulk transverse type, the suffix never shrinks.
    for v in range(13):
        assert all(a==448 for a,b,c,d in B[6,v] if c==448)
    assert all(b==192 for a,b,c,d in B[6,12] if d==192)
    assert all(448 not in (a,c) for a,b,c,d in B[6,0])
    if not star_at_near_end:
        assert all(c==384 for a,b,c,d in B[6,0] if d==448)
        assert all(a==384 for a,b,c,d in B[6,0] if b==448)
    for j in range(1 if star_at_near_end else 2,9):
        # Two consecutive rows whose east suffix starts at j, and the
        # preceding two columns; east fringe is outside this local box.
        left=defaultdict(list)
        if j>1:
            for a,b,c,d in B[6,min(j-2,6)]:left[b,d].append((a,c))
        links=defaultdict(set)
        for b,e,d,f in B[6,min(j-1,6)]:
            if e==f==448 and b!=448 and d!=448:
                if j==1:links[d,448].add((b,448))
                else:
                    for a,c in left[b,d]:links[c,d,448].add((a,b,448))
        n=6 if j==1 else 9
        def put(front,w):
            for l in (2,1,0):
                m=[bool(v&(1<<(3*l+b))) for v in w for b in range(3)]
                feet=([1] if j<=2 else [])+([n-1] if l==2 else [])
                try:front=push(front,m,feet)
                except AssertionError as ex:
                    if str(ex)!='forced cycle':raise
                    return
            return tuple(front[0]),tuple(front[1])
        rows=set(links)|{w for vs in links.values() for w in vs}
        st={(w,z) for w in rows if (z:=put((None,list(range(n+1))),w)) is not None}
        h=1;seen=set()
        while st and frozenset(st) not in seen:
            seen.add(frozenset(st));h+=1
            st={(y,s) for w,z in st for y in links[w] if (s:=put(z,y)) is not None}
        assert not st and h==(3 if j==1 else 4)
        print('suffix start',j,'plateau height bound',h-1)
if __name__=='__main__':check()
