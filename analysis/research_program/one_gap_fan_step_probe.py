"""Folded 15-row replay of the odd fan step using patch overlap only.
Each of the three middle bonds can loop any number of whole tiles.
"""
from .defect_window import table
from .north_fan_sync import fan
from functools import lru_cache
from itertools import product

A,C,R=16,19,16
ROWS=[fan(A+3*y,C-6*y,R+3*y) for y in range(3)]
W=3*len(ROWS[0]); H=15
# Each extra visit duplicates exactly three columns. The cuts lie
# inside constant runs of all three rows, not on a moving transition.
LOOPS=[3*x for x in (8,A+3+8,W//3-9)]

def chart(c):return c+1 if c<12 else 118-(W-c) if c>=W-12 else 16+c%3

def probe():
    typ,patch,star=table(119)
    @lru_cache(None)
    def domain(r,j):
        ts=[star(typ(0,17+r,j+1),tuple(range(4)),o,o==-1,False) for o in [-1,0,1,2,3]]
        def cross(m):return (m>>4&1)+2*(m>>5&1)+4*(m>>7&1)+8*(m>>3&1)+16*(m>>1&1)
        return {m for m,z in enumerate(patch(typ(1,16+r,j))) if z==0 and
                (min(j,116-j)<6 or any(t[cross(m)]==0 for t in ts))}
    cells={(r,c):{m for m in domain(r,chart(c)) if all(r+a>=6 or (m>>(3*a+b)&1)==
        (ROWS[(r+a)//3][(c+b)//3]>>(3*((c+b)%3)+(r+a)%3)&1) for a,b in product(range(3),repeat=2))}
        for r,c in product(range(H-2),range(W-2))}
    def ov(m,d):return [m&438,m&504,(m&219)<<1,(m&63)<<3][d]
    for t in range(400):
        changes=0
        old={k:v.copy() for k,v in cells.items()}
        for (r,c),ms in cells.items():
            for d,(dr,dc) in enumerate(((0,1),(1,0),(0,-1),(-1,0))):
                if d in (0,2):continue
                n=(r+dr,c+dc)
                if n not in cells:continue
                support=old[n]
                good={ov(m,(d+2)%4) for m in support};gone={m for m in ms if ov(m,d) not in good}
                ms-=gone;changes+=len(gone)
        # Arc deletion alone admits a cyclic explanation wholly inside a
        # repeated bond. Actual rows have a first and last column. Take
        # least (not greatest) horizontal reachability from both ends.
        for sign,origin in ((1,0),(-1,W-3)):
            for r in range(H-2):
                d=0 if sign==1 else 2; rev=2-d
                reachable=[set() for _ in range(W-2)];reachable[origin]=cells[r,origin].copy();todo=[origin]
                for c in todo:
                    outs=[c+sign];x=c-2 if sign==1 else c
                    if x in LOOPS:outs.append(c-2*sign)
                    keys={ov(m,d) for m in reachable[c]}
                    for k in outs:
                        if 0<=k<W-2:
                            new={m for m in cells[r,k]-reachable[k] if ov(m,rev) in keys}
                            if new:reachable[k]|=new;todo.append(k)
                for c,ms in enumerate(reachable):
                    changes+=len(cells[r,c]-ms);cells[r,c]=ms
        if not changes:break
    assert all(cells.values())
    def tr(m):return sum((m>>(3*b+a)&1)<<(3*a+b) for a,b in product(range(3),repeat=2))
    bad=[i for i,m in enumerate(ROWS[2]) if cells[6,3*i]!={tr(m)}]
    print('passes',t+1,'non-singleton or wrong output tiles',bad)
    assert not bad
    return cells
if __name__=='__main__':probe()
