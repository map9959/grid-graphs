"""Compute an outer bound for the scored rooted-route cover.

Start at tile row four with the rooted suffix only. The first
coordinate of each word is the physical (untransposed) NW mask.
Identical domains share calculations; tile assignments never do.
"""
from functools import lru_cache
from .east_rail_fold import catalogue

SHAPES = {9,72,73,2,66,16,128,129,132,36,258,288,292}


def support_cover(u, q, rooted, rim=False, trace=False, rows=False, minimal=False, snapshot=False):
    k = 11+14*u
    f = max(3,q+1)+12
    h,w = k-4,k-f
    if minimal: w=3*h//4+3
    base = catalogue()
    @lru_cache(None)
    def domain(rtag,ctag,top):
        vs = base[1 if rtag==6 else 40+rtag-14,
                  0 if ctag==6 else 33+ctag-14]
        out = set()
        for a,b,c,d in vs:
            if top and (a,b)!=(73,73): continue
            for x in ([True] if top or not rooted else [False,True]):
                for y in ([True] if top or not rooted else [False,True]):
                    def down(m,n):
                        return bool(m&8 and (m&64 or n&1))
                    def across(m,n):
                        return bool(m&2 and n&1)
                    z,t = x and down(a,c),y and down(b,d)
                    if rooted and ((x and y and across(a,b)) or (z and t and across(c,d))):
                        continue
                    if rim in (True,'east') and ctag==12 and ((y and b&2) or (t and d&2)):
                        continue
                    if rim in (True,'south') and rtag==12 and ((z and c&8) or (t and d&8)):
                        continue
                    out.add(tuple(2*m+int(rooted and v) for m,v in zip((a,b,c,d),(x,y,z,t))))
        return frozenset(out)
    grid = [[domain(max(6,14+r-h),max(6,14+c-w),r==0) for c in range(w-1)] for r in range(h-1)]
    sides=((0,1),(0,2),(2,3),(1,3))
    @lru_cache(maxsize=20000)
    def keys(ws,face):
        a,b=sides[face]
        return frozenset((v[a],v[b]) for v in ws)
    @lru_cache(maxsize=40000)
    def cut(ws,face,allowed):
        if keys(ws,face)<=allowed:return ws
        a,b=sides[face]
        return frozenset(v for v in ws if (v[a],v[b]) in allowed)
    for rnd in range(h+w):
        change=False
        for backward in (False,True):
            rr=range(h-2,-1,-1) if backward else range(h-1)
            cc=range(w-2,-1,-1) if backward else range(w-1)
            for r in rr:
                for c in cc:
                    old=ws=grid[r][c]
                    for dr,dc,i in ([(1,0,2),(0,1,3)] if backward else [(-1,0,0),(0,-1,1)]):
                        if 0<=r+dr<h-1 and 0<=c+dc<w-1:
                            ws=cut(ws,i,keys(grid[r+dr][c+dc],i^2))
                    if trace and old and not ws:
                        print("first empty",rnd,backward,r,c,flush=True)
                        trace=False
                    grid[r][c]=ws
                    change |= old is not ws and old!=ws
                if rows and rnd==0 and not backward:
                    starts=[c for c in range(w-1) if {v[3] for v in grid[r][c]}=={147}]
                    locked=[c for c in range(w-1) if grid[r][c] and all(v[3]%2 for v in grid[r][c])]
                    print(r+1,min(starts,default=None),min(locked,default=None))
            if snapshot:return grid
        if not change:break
    count=1+((k+3)//4-f)//16
    bad=set()
    for a in range(count):
        for j in range((k-21)//4):
            for r in range(1,10):
                for c in range(10):
                    y,x=4*j+r,16*a+3*j+c
                    if any(v[0]//2 not in SHAPES for v in grid[y][x]):bad.add((y+4,x+f))
    return count,bad,rnd+1


if __name__=="__main__":
    import sys
    u,q=map(int,sys.argv[1:3])
    for rooted,rim in [(False,False),(True,False),(True,True)]:
        count,bad,rounds=support_cover(u,q,rooted,rim)
        print(f"{u=} {q=} {rooted=} {rim=} {rounds=} routes={count} candidate bad sites={len(bad)}",flush=True)
