"""Catalogue implications and a rooted local test for plateaus of the west arm."""
import gzip,json
from pathlib import Path
from collections import defaultdict
from .neighbor_diagonal import push

def main():
    B={(u,v):ws for u,v,ws in json.loads(gzip.decompress(
        Path('target/tile_family_3_5_h6.json.gz').read_bytes()))}
    for (u,v),ws in B.items():
        if u<3:continue
        if v==0:
            assert all(c==6 for a,b,c,d in ws if a==6)
            assert all(d==7 for a,b,c,d in ws if a==c==6 and b==7)
        else:assert all(d==7 for a,b,c,d in ws if a==c==b==7)
    print('west-prefix nesting: checked',10*13,'star-free positional catalogues')
    ws=B[6,6];links=defaultdict(set)
    for a,b,c,d in ws:
        if a==c==7 and b!=7 and d!=7:
            for x,y,z,t in ws:
                if x==b and z==d:links[d,t].add((b,y))
    # Process bottom row first. Its two marks/mask choices and the
    # connectivity on the top physical row form a complete local state.
    def put(front,p):
        w=(7,*p)
        for l in (2,1,0):
            m=[bool(v&(1<<(3*l+j))) for v in w for j in range(3)]
            try:front=push(front,m,(0,) if l==0 else ())
            except AssertionError as e:
                if str(e)!='forced cycle':raise
                return
        return tuple(front[0]),tuple(front[1])
    ps=set(links)|{p for rows in links.values() for p in rows}
    st={(w,z) for w in ps if (z:=put((None,list(range(10))),w)) is not None}
    seen=set();n=1
    while st:
        print('plateau height',n,'live joint states',len(st))
        key=frozenset(st);assert key not in seen;seen.add(key)
        st={(y,s) for w,z in st for y in links[w] if (s:=put(z,y)) is not None}
        n+=1
    print('no plateau of',n,'tile rows in deep bulk')
if __name__=='__main__':main()
