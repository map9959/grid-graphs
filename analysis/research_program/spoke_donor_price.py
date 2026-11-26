"""Exact maximum gain for omitting separated, occupied wing spokes."""
from fractions import Fraction as Q
from .sparse_spoke_tile import layer,advance,loss

def maximum(alpha,gap=3):
    a,b=alpha.as_integer_ratio()
    C={s:b*z for s,z in layer(2,set()).items()};D=[C.copy()]+[{} for _ in range(gap-1)]
    seen={};peak=0
    def step(dp,o):return advance(dp,o,unit=b,premium=a)
    def merge(*ds):
        out={}
        for d in ds:
            for s,z in d.items():out[s]=max(out.get(s,z),z)
        return out
    for k in range(80):
        clean=step(step(C,False),False)
        old=step(step(merge(*D),False),False)
        w,_=loss(clean,old);peak=max(peak,w)
        u=max(C.values());v=max(z for d in D for z in d.values())
        norm=lambda d,h:frozenset((s,z-h) for s,z in d.items())
        sig=norm(C,u),tuple(norm(d,v) for d in D)
        if sig in seen:
            t,x,y=seen[sig]
            return (Q(peak,b) if v-y<=u-x else None),t,k,Q(v-y-u+x,b)
        seen[sig]=k,u,v
        C=step(C,False)
        D=[step(merge(D[0],D[1]),False),*[step(x,False) for x in D[2:]],step(D[0],True)]
    raise AssertionError('no repeat')

if __name__=='__main__':
    for gap,a,w in ((3,Q(1),Q(2)),(2,Q(1),None),(2,Q(1,2),Q(3,2))):
        cert=maximum(a,gap);assert cert[0]==w
        print('gap',gap,'donor price',a,'loss, repeat heights, drift:',cert,flush=True)
