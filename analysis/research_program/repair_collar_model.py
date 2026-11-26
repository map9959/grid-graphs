"""Attempt a physical collar model, composing corner patches across fixed flat side words."""
import sys
from itertools import product
from fractions import Fraction as Q
from pysat.solvers import Solver
from .diagonal_score import data,generate,DIR
from .patch_square import trans
from .repair_defect_budget import check_errors,charge

def test(n,depth,marg,pattern):
    k=n//3;T=3*k*k+(16*k-7)//3;tab=data(n,T);scale=tab[3]
    X=list(range(1,n*n+1));ids={('a',u,s):1+n*n+4*u+s for u in range(n*n) for s in range(4)}
    frozen={};sol={};dom=set()
    for turn,kind in enumerate(pattern):
        phase=int(kind) if kind.isdigit() else 0
        normal=kind=='N' or kind.isdigit()
        for d,j in product(range(depth),range(marg,n-marg)):
            y,x=trans(d,j,n,turn);dom.add((y,x))
            z=(j-phase)%3
            bit=(d==0 or d>=2 and z==0) if normal else d%3==0
            if normal and d>=2:v=(d-1,j) if z==0 else (d,j+(-1 if z==1 else 1))
            elif d%3==0:v=d,j+(-1 if turn<2 else 1)
            else:v=d+(-1 if d%3==1 else 1),j
            yy,xx=trans(*v,n,turn);frozen[y,x]=bit,DIR.index((yy-y,xx-x))
    sol.update(frozen);total=0
    for turn in range(4):
        D={trans(i,j,n,turn) for i,j in product(range(marg+4),repeat=2) if min(i,j)<depth}
        dom.update(D);budget=tab[4];best=None
        limits=next(([Q(z) for z in opt.split('=')[1].split(',')] for opt in sys.argv if opt.startswith('--prices=')),None)
        for limit in ([limits[turn]] if limits else (Q(1,3),Q(2,3),Q(7,6))):
            ix={};f,xs=generate(n,T,D,limit==0,(*tab[:4],int(limit*scale)),variables=ix)
            for y,x in D&frozen.keys():
                bit,out=frozen[y,x];f.append([xs[y*n+x]*(1 if bit else -1)]);f.append([ix['a',y*n+x,out]])
            if f'--hole={turn}' in sys.argv:
                opts=[]
                for y,x in D:
                    if x not in (3,n-4) or not 9<=y<n-9:continue
                    near=[(y+i,x+j) for i,j in ((0,-2),(0,-1),(0,1),(0,2),(-1,-1),(-1,1),(1,-1),(1,1))]
                    if not all(v in D for v in near):continue
                    u=f.nv+1;f.append([-u,-xs[y*n+x]]);f.append([-u,*[xs[i*n+j] for i,j in near]]);opts.append(u)
                f.append(opts)
            with Solver(name='cadical195',bootstrap_with=f.clauses) as s:
                s.conf_budget(30000);ok=s.solve_limited()
                if ok:
                    truth={a for a in s.get_model() if a>0}
                    val,_=charge(n,D,tab,xs,ix,truth)
                    bits={(y,x):(xs[y*n+x] in truth,next((z for z in range(4) if ix.get(('a',y*n+x,z)) in truth),-1)) for y,x in D}
                    best=val,bits;break
            print('corner',turn,'cutoff',limit,ok,flush=True)
        if best is None:return
        val,bits=best;sol.update(bits);total+=val
        print('corner',turn,'true price',Q(val,scale),flush=True)
    truth=set()
    for (y,x),(bit,out) in sol.items():
        u=y*n+x
        if bit:truth.add(X[u])
        if out>=0:truth.add(ids['a',u,out])
    val,cap=charge(n,dom,tab,X,ids,truth)
    assert val==total and len(dom)==n*n-(n-2*depth)**2
    print('whole-collar charge',Q(val,scale),'budget',Q(cap,scale),'errors',check_errors(n,lambda i,j:sol.get((i,j),(False,))[0]))
    if '--save' in sys.argv:
        from .repair_collar_replay import audit,save
        audit(sol,tab);save(sol)
if __name__=='__main__':test(103,12,int(sys.argv[1]),sys.argv[2])
