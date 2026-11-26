"""Probe the retained-core envelope with partially split interior rails."""
from functools import lru_cache
from .extend_forest_28 import verify

@lru_cache(65536)
def moves(h,old,part,back,which,reset,bar=True):
    # Roots: north tree, solid south rim, a private interrupted rail.
    # The last live group can be forgotten, even if its frontier survives.
    if reset:
        v=list(part);v[2]=-1;part=tuple(v.index(x) for x in v)
    res=[];off=h+3
    for mask in range(1<<h):
        if mask&(old<<1|old>>1) or not back and mask&1:continue
        q=[*part,*range(off,off+h)]
        def rt(i):
            while i!=q[i]:i=q[i]
            return i
        def join(i,j):
            a,b=rt(i),rt(j);q[a]=b;return a!=b
        if (back or mask&1) and not join(which,off):continue
        if bar and mask>>(h-1)&1 and not join(1,off+h-1):continue
        if not all(join(off+i,off+i+1) for i in range(h-1) if mask>>i&3):continue
        if not all(join(3+i,off+i) for i in range(h) if (mask|old)>>i&1):continue
        v=[rt(i) for i in (0,1,2,*range(off,off+h))]
        res.append((mask,tuple(v.index(x) for x in v)))
    return res

def cap(n,h,through,bar=True):
    dp={(0,tuple(range(3+h))):(0,0)}
    for x in range(n):
        center=3*((x+1)//3);nd={}
        for (old,p),(v,w) in dp.items():
            for k in moves(h,old,p,x==center,0 if center in through else 2,x%3==2,bar):
                z=v+k[0].bit_count()
                if k not in nd or z>nd[k][0]:nd[k]=z,(w<<h)|k[0]
        dp=nd
    _,word=max(dp.values())
    return [''.join('#' if word>>(h*(n-1-x)+j)&1 else '.' for x in range(n)) for j in range(h)]

def capped(n,h,hn=0,extras=None):
    through={x for x in range(0,n,3) if x<10 or x>=n-10}
    through.update([3*(n//6)] if extras is None else extras)
    north=cap(n,hn,set())[::-1] if hn else []
    rows=['#'*n,'.'*n]+north+['#..'*(n//3)+'#']*(n-h-hn-4)
    for y in (n//2-1,n//2):rows[y]=''.join('#' if x in through else '.' for x in range(n))
    r=rows+cap(n,h,through)+['.'*n,'#'*n]
    return verify(r,True)

if __name__=='__main__':
    from .core_boundary_envelope import prices,accounting
    from .arbitrary_collar_transfer import marks
    r=capped(103,4,extras=[]);c=[s[10:-10] for s in r[10:-10]];T=marks(r)-marks(c)
    a,(D,cc,rr,_,pairs)=accounting(c);raw=(83**2+D-cc-rr)//3
    assert pairs==27 and a==2217 and T+raw==3647
    print('physical tree',verify(r),'split pairs',pairs,'without / with witness charge',T+raw,T+a)
