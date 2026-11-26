"""0011, NW sink: width-six physical projection specialized to exit phase.

The only cycle test is the perimeter of a 5-row by 4-column rectangle
with its top edge on the north side. There are no frontier partitions.
"""
from functools import lru_cache
from .defect_window import table, DIR
from .seven_threshold import masks
from .sector_oriented import assign
from .odd_frames import frame


def run(n, arcs=True):
    H = 6
    typ, patch, star = table(n)
    marks = frame(n, (0, 0, 1, 1))

    @lru_cache(None)
    def options(j):
        return [m for m in range(64)
                if all(((m>>r)&1) == marks[r,j] for r in range(H) if (r,j) in marks)]

    @lru_cache(None)
    def transitions(j,t,a,b,west):
        out = []
        first,last = j == 0,j == n-1
        for c in ([0] if last else options(j+1)):
            if c&((b<<1)|(b>>1)): continue
            if not (first or last) and any(patch(typ(1,r,j-1))[m] for r,m in enumerate(masks(a,b,c,H))):
                continue
            if not last and all((m|(m>>1))&15 == 15 for m in (t,c)) and all(
                    (x|y)&17 == 17 for x,y in ((t,a),(a,b),(b,c))):
                continue
            dom = []
            for r in range(H-1):
                ds = tuple(i for i,(y,x) in enumerate(DIR) if 0<=r+y<n and 0<=j+x<n)
                nb = (c>>r,b>>(r+1),a>>r,b>>(r-1) if r else 0)
                ix = ((b>>r)&1)+sum((nb[i]&1)<<(k+1) for k,i in enumerate(ds))
                # Only the NW root is fixed; non-isolated nonroots have a parent.
                allow = dict()
                for o in (-1,*ds):
                    v = star(typ(0,r,j),ds,o,(r,j)==(0,0),len(ds)==2)[ix]
                    if v==0 or (v==72 and r==0 and o==1 and 3<=j<n-1 and j!=n-3):
                        allow[o]=v
                dom.append(allow)
            if not all(dom): continue
            if arcs:
                for nw,dirs in assign(b,west,0 if last else b|c,H):
                    if all(o in opts for opts,o in zip(dom,dirs)):
                        charge = dom[0][dirs[0]]
                        out.append((a,b,c,nw,(1+j%3 if charge else 0)))
            else:
                for charge in set(dom[0].values()):
                    out.append((a,b,c,0,(1+j%3 if charge else 0)))
        return out

    states={(0,0,b,0,0) for b in options(0)}
    seen={}
    peak=0
    for j in range(n):
        if j%3==0 and 12<=j<n-12: seen[j]=states
        tag = j if j<12 or j>=n-12 else 12+j%3
        states={(*nxt,paid or q) for t,a,b,w,paid in states
                for *nxt,q in transitions(tag,t,a,b,w) if not (paid and q)}
        peak=max(peak,len(states))
    repeat=next(((i,j,len(seen[i])) for i in seen for j in seen
                 if j-i==42 and seen[i]==seen[j]),None)
    return {q for *_,q in states},repeat,peak


if __name__=="__main__":
    for n in (35,77,119):
        result=run(n)
        assert result[0] == {3}  # nonzero labels are 1+exit column modulo 3
        if n == 119:
            assert result[1] == (42,84,208)
        print(n,result,flush=True)
