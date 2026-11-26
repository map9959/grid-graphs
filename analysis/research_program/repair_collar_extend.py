"""Reopen the inner edge of the error witness with an exact residual budget."""
from .repair_collar_replay import load,domain,audit,best_orientation
from .repair_defect_budget import charge,data,generate,DIR,sys
from .sector_gap_cover import verify
from pysat.solvers import Solver

def test(fixed,depth):
    assert 3<=fixed<=12 and depth>=fixed+1
    n=103;tab=data(n,3647);sol=load();outer=domain(n,fixed-1);marks=domain(n,fixed)
    strip=domain(n,depth)-domain(n,fixed-3);N=n*n
    X=list(range(1,N+1));ids={('a',u,s):1+N+4*u+s for u in range(N) for s in range(4)};true=set()
    for (i,j),(m,out) in sol.items():
        u=i*n+j
        if m:true.add(X[u])
        if out>=0:true.add(ids['a',u,out])
    old=charge(n,outer,tab,X,ids,true)[0]-charge(n,outer&strip,tab,X,ids,true)[0]
    free='--free-arrows' in sys.argv
    if free:
        outer=marks;strip=domain(n,depth)-domain(n,fixed-2)
        radius=next((int(z.split('=')[1]) for z in sys.argv if z.startswith('--south=')),None)
        if radius:
            from .patch_square import trans
            boxes=[{trans(i,j,n,g) for i in range(radius) for j in range(radius)} for g in (2,3)]
            old=sum(best_orientation({u:sol[u] for u in marks&d},tab,strip) for d in boxes)
            # Restrict the annulus proof itself as well. Independent
            # lower bounds above were charged only outside this strip.
            only=next((int(z.split('=')[1]) for z in sys.argv if z.startswith('--inner-corner=')),None)
            strip&=set.union(*(boxes if only is None else [boxes[only-2]]))
        else:old=best_orientation({u:sol[u] for u in marks},tab,strip)
    residual=tab[4]-old
    ix={};f,xs=generate(n,3647,strip,False,(*tab[:4],residual),variables=ix)
    for i,j in strip&marks:
        u=n*i+j;m,out=sol[i,j];f.append([xs[u]*(1 if m else -1)])
        if not free and (i,j) in outer:
            for s in range(4):
                if ('a',u,s) in ix:f.append([ix['a',u,s]*(1 if s==out else -1)])
    with Solver(name='cadical195',bootstrap_with=f.clauses) as s:
        s.conf_budget(30000);ans=s.solve_limited()
        print('fixed marking depth',fixed,'tested depth',depth,'outer charge',old,'strip solver',ans,flush=True)
        if ans:
            truth={v for v in s.get_model() if v>0}
            local=charge(n,strip,tab,xs,ix,truth)[0]
            print('strip charge plus outer bound',local+old,'budget',tab[4],flush=True)
            if local<=residual and not free:
                extended={v:sol[v] for v in outer-strip}
                for i,j in strip:
                    u=i*n+j;extended[i,j]=(int(xs[u] in truth),next((s for s in range(4) if ix.get(('a',u,s)) in truth),-1))
                assert audit(extended,tab)==local+old
        elif ans is False or '--drat' in sys.argv:
            ok=verify(f,f'repair_extend103_{fixed}_{depth}')
            if ans is False:assert ok
if __name__=='__main__':test(int(sys.argv[1]),int(sys.argv[2]))
