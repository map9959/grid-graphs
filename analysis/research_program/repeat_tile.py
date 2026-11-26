"""Search for a repeatable cylinder tile with boundary bonus 4/9 per column."""
from itertools import product,combinations
from pathlib import Path
from .square_dual_physical import DIR
def run(W,H):
    from pysat.formula import CNF,IDPool
    from pysat.card import CardEnc,EncType
    from pysat.solvers import Solver
    from .extend_forest_28 import verify
    assert W%9==0
    p=IDPool();f=CNF()
    m=lambda i,j:p.id(('m',i,j%W))
    arrow=lambda i,j,d:p.id(('a',i,j%W,d))
    for i,j in product(range(H),range(W)):
        ds=[d for d,(a,b) in enumerate(DIR) if 0<=i+a<H]
        if i in (H//2,H//2+1):f.append([m(i,j) if j%3==0 else -m(i,j)])
        if '--bars' in __import__('sys').argv and i in (0,H-1):f.append([m(i,j)])
        for d,e in combinations(ds,2):f.append([-arrow(i,j,d),-arrow(i,j,e)])
        for d in ds:
            a,b=DIR[d];x,y=i+a,(j+b)%W;u=arrow(i,j,d);v=arrow(x,y,(d+2)%4)
            if d<2:
                f.extend([[-u,-v],[-m(i,j),u,v],[-m(x,y),u,v],[-u,m(i,j),m(x,y)],[-v,m(i,j),m(x,y)]])
            for e,(di,dj) in enumerate(DIR):
                if e==(d+2)%4 or not 0<=x+di<H:continue
                s=p.id(('sheet',i,j));t=p.id(('sheet',x,y))*(-1 if abs(e-d)==3 else 1);g=[-u,-arrow(x,y,e)]
                f.extend([g+[-s,t],g+[s,-t]])
        if i+1<H:
            for a in (-1,1):f.append([-m(i,j),-m(i+1,j+a)])
    cells=[m(i,j) for i,j in product(range(H),range(W))]
    goal=W*H//3+4*W//9
    f.extend(CardEnc.atleast(cells,bound=goal,vpool=p,encoding=EncType.cardnetwrk).clauses)
    with Solver(name='cadical195',bootstrap_with=f.clauses) as s:
        s.conf_budget(150000);ok=s.solve_limited()
        print('repeat candidate width',W,'height',H,'target',goal,'status',ok,flush=True)
        if ok:
            chosen={v for v in s.get_model() if v>0};tile=[''.join('#' if m(i,j) in chosen else '.' for j in range(W)) for i in range(H)]
            n=1+W*((H+W)//W);rows=tile[:H//2]+[tile[H//2]]*(n-H)+tile[H//2:]
            rows=[(r*(n//W+1))[:n] for r in rows];print('physical replay',n,verify(rows),flush=True)
            Path(f'target/repeat_tile_{W}_{H}.txt').write_text('\n'.join(tile)+'\n')
if __name__=='__main__':
    import sys
    run(*map(int,sys.argv[1:3]))
