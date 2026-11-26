"""Uniform two-gap rail exchange obstruction using exact affine integer sets."""
from ctypes import CDLL,c_void_p,c_int,c_char_p,c_long,CFUNCTYPE
from ctypes.util import find_library
from functools import lru_cache
from itertools import combinations,product

lib=CDLL(find_library('isl'))
def fn(name,ret,*args):
    f=getattr(lib,'isl_'+name);f.argtypes=list(args);f.restype=ret;return f
ptr=c_void_p
ctx=fn('ctx_alloc',ptr)()
parse=fn('set_read_from_str',ptr,ptr,c_char_p)
cp=fn('set_copy',ptr,ptr);drop=fn('set_free',ptr,ptr)
inter=fn('set_intersect',ptr,ptr,ptr);minus=fn('set_subtract',ptr,ptr,ptr)
union=fn('set_union',ptr,ptr,ptr);empty=fn('set_is_empty',c_int,ptr)
coalesce=fn('set_coalesce',ptr,ptr)
class Set:
    def __init__(self,p):assert p;self.p=p
    def __del__(self):drop(self.p)
    def __and__(a,b):return Set(inter(cp(a.p),cp(b.p)))
    def __sub__(a,b):return Set(minus(cp(a.p),cp(b.p)))
    def __or__(a,b):return Set(coalesce(union(cp(a.p),cp(b.p))))
    def none(self):
        v=empty(self.p);assert v in (0,1);return bool(v)
def expr(s):return Set(parse(ctx,('{ [t,i,j] : t >= 0 and ('+s+') }').encode()))
O=(0,0);D=((0,1),(1,0),(0,-1),(-1,0));cross=(O,*D)
diag=tuple(product((-1,1),repeat=2))
plus=lambda a,b:(a[0]+b[0],a[1]+b[1])
def close(u):return {plus(u,v) for v in cross}
def geometry():
    N='(35+42t)';F='(5+7t)';M='(6+6t)'
    @lru_cache(None)
    def inside(u):
        a,b=u;return expr(f'1<=i+{a}< {N}-1 and 1<=j+{b}< {N}-1')
    @lru_cache(None)
    def marks(u):
        a,b=u;r=f'(i+{a})';c=f'(j+{b})';L=f'(3*{r}-9)';R=f'({N}-1-{L})'
        h=f'({r}-3-{F})'
        reg=lambda l:f'(({c}<={l} and {c}%3=0) or ({c}>={l}+4 and ({N}-1-{c})%3=0))'
        cases=[f'{r}=0 and ({c}<{N}-3 or {c}={N}-1)',f'{r}=1 and {c}={N}-1',
               f'{r}=2 and (({c}%3=2 and {c}<{N}-1) or {c}={N}-1)',
               f'3<={r}<{F}+3 and (({c}<={L} and {c}%3=0) or ({c}>={R} and ({N}-1-{c})%3=0) or ({L}+5<={c}<{R}-4 and {c}%3=2))',
               f'exists (b: 0<={h}-7b<=6 and 0<={h} and {r}<{N}-5 and ('+
               # l = 3F-3b. Last incomplete band consists only of phase zero.
               f'({reg("(15+21t-3b)")} and ({h}-7b<=4 or {c}!=15+21t-3b)) or '+
               f'(({h}-7b=2 or {h}-7b=5) and {c}=17+21t-3b) or ({h}-7b=6 and {c}=14+21t-3b)))',
               f'{N}-5<={r}<={N}-3 and (({c}<{M}-5 and {c}%3=0) or ({c}>={M}+4 and ({N}-1-{c})%3=0) or '+
               f'({r}={N}-5 and {c}={M}+2) or ({r}={N}-4 and {M}-4<={c}<{M}) or ({r}={N}-3 and {c}={M}+1))',
               f'{r}={N}-1']
        return expr(f'0<={r}<{N} and 0<={c}<{N} and ('+' or '.join('('+x+')' for x in cases)+')')
    return inside,marks

def run():
    inside,marks=geometry()
    from .zipper_rails import build
    cb=CFUNCTYPE(c_int,ptr,ptr)
    foreach=fn('set_foreach_point',c_int,ptr,cb,ptr)
    coord=fn('point_get_coordinate_val',ptr,ptr,c_int,c_int)
    numer=fn('val_get_num_si',c_long,ptr)
    freeval=fn('val_free',ptr,ptr);freept=fn('point_free',ptr,ptr)
    for t in (2,3):
        points=set()
        @cb
        def visit(pt,_):
            vals=[coord(pt,3,k) for k in (1,2)] # isl_dim_set
            points.add(tuple(numer(z) for z in vals))
            for z in vals:freeval(z)
            freept(pt);return 0
        board=marks(O)&expr(f't={t}')
        assert foreach(board.p,visit,None)==0
        assert points=={(i,j) for i,row in enumerate(build(35+42*t)) for j,b in enumerate(row) if b=='#'}
        print('affine mark set equals physical rail at',35+42*t,len(points),'sites')
    # Test the explicit three edits symbolically: x is a singleton, y
    # bridges two marks, z extends one. Each has the claimed neighborhood
    # throughout the progression and their affected neighborhoods are disjoint.
    for at,old,degree in [('i=10+7t and j=17+21t',1,0),
                          ('i=29+42t and j=8+6t',0,2),('i=2 and j=3',0,1)]:
        pos=expr(at)
        assert (pos-marks(O) if old else pos&marks(O)).none()
        present=[d for d in D if not (pos&marks(d)).none()]
        assert len(present)==degree and all((pos-marks(d)).none() for d in present)
        assert all((pos&marks(d)).none() for d in diag)
    print('explicit edit: +1 mark, +3 marked adjacencies, deleted center remains isolated, all t>=0')
    # Candidate deletion x must have marked degree at most one.
    xs=marks(O)&inside(O)
    for a,b in combinations(D,2):xs=xs-(marks(a)&marks(b))
    # lost[u]: u+x loses its last marked neighbor (including itself).
    lost={}
    for u in cross:
        z=xs
        for v in close(u)-{O}:z=z-marks(v)
        lost[u]=z
    no_loss=xs
    for z in lost.values():no_loss=no_loss-z
    assert no_loss.none()
    offsets=sorted(set.union(*(close(u) for u in cross))-{O})
    ok={}
    for y in offsets:
        z=(xs&inside(y))-marks(y)
        for d in diag:
            v=plus(y,d)
            if v!=O:z=z-marks(v)
        ok[y]=z
        single=z
        for u in set(cross)-close(y):single=single-lost[u]
        assert single.none()
    print('all t>=0: every eligible deletion loses coverage; one admissible insertion never restores it',flush=True)
    # Both insertions now lie within L1 distance two of the deletion.
    tested=0;coverable=0;peak=-100
    for y,z in combinations(offsets,2):
        if (z[0]-y[0],z[1]-y[1]) in diag:continue
        tested+=1;A=ok[y]&ok[z]
        for u in set(cross)-(close(y)|close(z)):A=A-lost[u]
        if A.none():continue
        coverable+=1
        # Count net marked edges as a signed sum of neighboring mark bits.
        from collections import Counter
        mult=Counter(v for p in (y,z) for v in close(p)-{p,O})
        mult.subtract(D)
        bins={int(z in close(y)):A}
        for v,w in mult.items():
            if not w:continue
            nxt={}
            for s,Z in bins.items():
                for k,V in ((s,Z-marks(v)),(s+w,Z&marks(v))):
                    if not V.none():nxt[k]=V if k not in nxt else nxt[k]|V
            bins=nxt
        assert 3 not in bins;peak=max(peak,max(bins))
    print('offset pairs tested',tested,'coverage-restoring pairs',coverable,'largest net marked adjacency gain',peak,'required',3)
if __name__=='__main__':run()
