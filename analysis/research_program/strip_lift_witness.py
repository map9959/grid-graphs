"""Side-19 strip-lift separation directly from two pinned physical patches."""
from fractions import Fraction as Q
import json
from pathlib import Path
from .patch_square import MASKS,SYM,trans,relaxation


def run(replacement=False):
    n=19;side=n-2;depth=5
    names,rows,obj=relaxation(n,6,pooled=2,period=3,strip_cut='lift' if replacement else True)
    path=Path(__file__).with_name('side19_lift_primal.json' if replacement else 'strip_period_primal_r1.json')
    vals={x:Q(v if replacement else v[0]) for x,v in json.loads(path.read_text()).items()}
    assert min(vals.values())>=0 and sum(w*vals.get(x,0) for x,w in obj.items())==141
    for row,op,b in rows:
        v=sum(w*vals.get(x,0) for x,w in row)
        assert {'=':v==b,'<=':v<=b,'>=':v>=b}[op]
    i,j0,event=(1,3,(0,)*6) if replacement else (0,2,(1,0)*3)
    def axis(t):
        return t if t<depth else 2*depth+3-side+t if t>=side-depth else depth+(t-depth)%3
    def mass(j,m):
        assert sum(axis(i)==axis(j) for i in range(side))==1
        pos=[tuple(axis(t) for t in trans(i,j,side,g)) for g in range(8)]
        return vals.get(names['p',min(zip(pos,SYM[m]))],0)
    sides=[]
    for j,start in [(j0,1),(j0+1,0)]:
        assert sum(mass(j,m) for m in MASKS)==1
        p=sum(mass(j,m) for m in MASKS if
              tuple((m>>(3*r+c))&1 for r in range(3) for c in (start,start+1))==event)
        sides.append(p)
    print('score 141, verified rows',len(rows),'origin',(i,j0),'shared event',event,'left and right probabilities:',*sides)
    assert sides[0]-sides[1]==(Q(1,2) if replacement else Q(1,4))


if __name__=='__main__':
    import sys
    run('--replacement' in sys.argv)
