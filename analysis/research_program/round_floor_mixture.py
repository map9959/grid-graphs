"""Try to realize each exact coarse-tree certificate member on one physical board."""
from pathlib import Path
from itertools import product
import json,sys
from .integral_rank_floor import Floor
from .skeleton_exit_chart import arrow_stage,DIR
from .skeleton_rooted_mixture import oracle


def trees():
    keys=sorted({arrow_stage(i,j,s,103,4,4) for i,j in product(range(0,103,3),repeat=2)
                 for s,(di,dj) in enumerate(DIR) if 0<=i+3*di<103 and 0<=j+3*dj<103})
    mix=json.loads(Path(__file__).with_name('skeleton_exit_rooted_mixture.json').read_text())
    p,run=oracle(103,keys,parents=True)
    try:
        for w,q in mix:yield run(w)
    finally:p.stdin.close();assert p.wait()==0


def literals(model,to):
    m=model.n//3+1
    for u,v in enumerate(to[1:],1):
        i,j=divmod(u,m);a,b=divmod(v,m)
        yield model.O[3*i,3*j][DIR.index((a-i,b-j))]


def turn_price(to):
    m=int(len(to)**.5);h=[0]*len(to);v=h.copy()
    for u,w in enumerate(to[1:],1):
        ls=h if u//m==w//m else v
        ls[u]+=1;ls[w]+=1
    return sum(map(min,h,v))


if __name__=='__main__':
    union='--union' in sys.argv
    selected={int(x) for x in sys.argv[1:] if x.isdigit()} or set(range(20))
    model=Floor(103,43)
    if '--cross' in sys.argv:
        from .integral_floor_cross import add_cross
        model.cross=(51,51,*add_cross(model,51,51,79))
    pick=[];cost=[]
    for t,to in enumerate(trees()):
        if t not in selected:continue
        cost.append(turn_price(to))
        if union:
            s=model.p.id();pick.append(s)
            for lit in literals(model,to):model.f.append([-s,lit])
        else:model.solve(f'integral tree {t}',15,list(literals(model,to)))
    print('coarse turn prices',cost,flush=True)
    if union:
        model.f.append(pick)
        assert model.solve('all listed integral trees',60)[0]=='UNSAT'
