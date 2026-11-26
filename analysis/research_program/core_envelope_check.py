"""Check path and cycle prices independently on small physical cores."""
from itertools import product
from .core_boundary_envelope import accounting,extend
from .sparse_component_exchange import graph
from .wired_crop_exchange import ring
from .core_interface_length import penalty,uniform
from .collar_vacancies import comb

def checks():
    tested=0
    for bits in range(16):
        pts={(i//2,i%2) for i in range(4) if bits>>i&1}
        base=[''.join('#' if (y,x) in pts else '.' for x in range(2)) for y in range(2)]
        try:graph(base,set())
        except AssertionError:continue
        for cyc in (False,True):
            n=3+cyc;p={(i+1,j+1) for i,j in pts}
            sites=ring(n) if cyc else [(0,i) for i in (2,1,0)]+[(1,0),(2,0)]
            best=-1
            for bs in product((0,1),repeat=len(sites)):
                tested+=1;z=sum(bs)
                if z<=best:continue
                M=p|{q for b,q in zip(bs,sites) if b}
                r=[''.join('#' if (i,j) in M else '.' for j in range(n)) for i in range(n)]
                try:graph(r,set())
                except AssertionError:continue
                best=z
            assert extend(base,4 if cyc else 0)[0]==best
    for b in product(range(3),repeat=5):
        v=min(sum((140 if x else 102) for j,x in enumerate(a) if not j or x!=a[j-1])+
              sum(-4+21*c for x,c in zip(a,b) if not x) for a in product((0,1),repeat=5))
        assert v==penalty(b)
    for n in (172,175,178):assert uniform(n)<=comb(n)
    print(tested,'physical rim/L masks considered; all feasible maxima matched;',
          '243 interval words and three rounding bases passed')
if __name__=='__main__':checks()
