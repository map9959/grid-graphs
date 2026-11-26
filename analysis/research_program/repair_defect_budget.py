"""Joint two-axis frame-error test, with one physical charge ledger."""
from itertools import product
import sys
from fractions import Fraction
from pysat.formula import IDPool
from pysat.solvers import Solver
from .diagonal_score import data,generate,DIR

def add_errors(f,X,n):
    pool=IDPool(start_from=f.nv+1);shared={}
    def site(y,x):return X[n*y+x]
    def either(ls):
        ls=tuple(sorted(set(ls)))
        if ls not in shared:
            v=pool.id();f.append([-v,*ls]);shared[ls]=v
        return shared[ls]
    def axis(flip):
        def m(y,x):return site(x,y) if flip else site(y,x)
        def hole(y,x):
            near=[m(y+i,x+j) for i,j in ((0,-2),(0,-1),(0,1),(0,2),(-1,-1),(-1,1),(1,-1),(1,1))]
            k=(m(y,x),tuple(near))
            if k not in shared:
                v=pool.id();f.append([-v,-k[0]]);f.append([-v,*near]);shared[k]=v
            return shared[k]
        def side(ys):return [hole(y,x) for y in ys for x in (3,n-4)]
        def end(y):
            return [m(y,x) if x%3 else hole(y,x) for x in range(3,n-3)]
        g=either(side(range(9,n-9)))
        left=[either(end(a)+side(range(a,9))) for a in range(1,10)]
        right=[either(end(n-1-b)+side(range(n-9,n-b))) for b in range(1,10)]
        for l,r in product(left,right):f.append([g,l,r])
    axis(False);axis(True)

def check_errors(n,mark):
    out=[]
    for flip in (False,True):
        m=lambda y,x:mark(x,y) if flip else mark(y,x)
        def witness(y,x):return not m(y,x) and any(m(y+i,x+j) for i,j in
                    ((0,-2),(0,-1),(0,1),(0,2),(-1,-1),(-1,1),(1,-1),(1,1)))
        common=[(y,x) for y in range(9,n-9) for x in (3,n-4) if witness(y,x)]
        num=0
        for a,b in product(range(1,10),repeat=2):
            y1=n-1-b
            err=any(m(y,x) for y in (a,y1) for x in range(3,n-3) if x%3)
            err|=any(witness(y,x) for y in (a,y1) for x in range(3,n-3,3))
            err|=any(witness(y,x) for y in range(a,y1+1) for x in (3,n-4))
            num+=err
        out.append((num,len(common),common[:1]))
    return out

def charge(n,dom,tables,X,ids,true):
    pos,patch,star,sc,cap=tables;cost=0
    m=lambda i,j:int(X[i*n+j] in true)
    for i,j in dom:
        ds=tuple(s for s,(a,b) in enumerate(DIR) if 0<=i+a<n and 0<=j+b<n)
        near=[(i+DIR[s][0],j+DIR[s][1]) for s in ds]
        if all(v in dom for v in near):
            u=i*n+j;o=next((s for s in ds if ids['a',u,s] in true),-1)
            cost+=star(pos(i,j,0),ds,len(ds)==2 and u!=0)[o][m(i,j)+sum(m(*v)<<(k+1) for k,v in enumerate(near))]
        if all((i+a,j+b) in dom for a,b in product(range(3),repeat=2)):
            cost+=patch(pos(i,j,1))[sum(m(i+a,j+b)<<(3*a+b) for a,b in product(range(3),repeat=2))]
    return cost,cap

def test(n,depth):
    k=n//3;t=3*k*k+(16*k-7)//3;tables=data(n,t)
    cutoff=next((Fraction(z.split('=')[1]) for z in sys.argv if z.startswith('--cutoff=')),None)
    orig=tables
    if cutoff is not None:
        q=tables[3]*cutoff
        budget=(q.__ceil__()-1) if '--strict' in sys.argv else int(q)
        assert 0<budget<=tables[4]
        tables=(*tables[:4],budget)
    dom={(i,j) for i,j in product(range(n),repeat=2) if min(i,j,n-1-i,n-1-j)<depth}
    if '--flat-pair' in sys.argv:
        col=next((int(z.split('=')[1]) for z in sys.argv if z.startswith('--at=')),n//2)
        patch=set(product(range(depth),range(col-12,col+13)))
        if '--join' in sys.argv:
            patch.update(product(range(depth,col+5),range(col-4,col+5)))
        dom=patch|{(j,i) for i,j in patch}
        if '--quadrant' in sys.argv:dom.update(product(range(col+5),repeat=2))
    ids={};bill={};f,X=generate(n,t,dom,'--zero' in sys.argv,tables,variables=ids,bill=bill)
    if '--control' not in sys.argv:add_errors(f,X,n)
    pattern=next((z.split('=')[1] for z in sys.argv if z.startswith('--model-sides=')),None)
    if pattern:
        # Witness search only: fixed optional completions are not necessary.
        from .patch_square import trans
        margin=next((int(z.split('=')[1]) for z in sys.argv if z.startswith('--margin=')),18)
        for turn,kind in enumerate(pattern):
            for d,j in product(range(depth),range(margin,n-margin)):
                y,x=trans(d,j,n,turn)
                bit=(d==0 or d>=2 and j%3==0) if kind=='N' else d%3==0
                f.append([X[y*n+x]*(1 if bit else -1)])
                if '--fix-arrows' in sys.argv:
                    tang=-1 if turn<2 else 1
                    if kind=='N' and d>=2:
                        u,v=(d-1,j) if j%3==0 else (d,j+(-1 if j%3==1 else 1))
                    elif d%3==0:u,v=d,j+tang
                    else:u,v=d+(-1 if d%3==1 else 1),j
                    yy,xx=trans(u,v,n,turn);dr=DIR.index((yy-y,xx-x))
                    f.append([ids['a',n*y+x,dr]])
    if '--flat-pair' in sys.argv:
        rad=next((int(z.split('=')[1]) for z in sys.argv if z.startswith('--radius=')),0)
        for i,(y0,x0) in enumerate(((3,col),(col,3))):
            if f'--skip={i}' in sys.argv:continue
            sel=[]
            for j in range(-rad,rad+1):
                y,x=y0+i*j,x0+(1-i)*j
                u=f.nv+1;sel.append(u);f.append([-u,-X[y*n+x]])
                if '--any-neighbor' in sys.argv:
                    offsets=((0,-2),(0,-1),(0,1),(0,2),(-1,-1),(-1,1),(1,-1),(1,1))
                    f.append([-u,*[X[(y+(dy if i else dx))*n+x+(dx if i else dy)] for dy,dx in offsets]])
                else:f.append([-u,X[(y-int(i==0))*n+x-int(i==1)]])
            f.append(sel)
    fence=next((int(z.split('=')[1]) for z in sys.argv if z.startswith('--fence=')),None)
    if fence is not None:
        assert '--flat-pair' in sys.argv and fence in (0,1)
        for d,j in product(range(depth),range(col-12,col+13)):
            if d>=depth-2 or abs(j-col)>=11:
                y,x=(j,d) if fence else (d,j)
                f.append([X[y*n+x]*(1 if d%3==0 else -1)])
    bound=next((int(z.split('=')[1]) for z in sys.argv if z.startswith('--search-bound=')),None)
    if bound is not None:
        from pysat.pb import PBEnc
        f.extend(PBEnc.atmost(lits=list(bill),weights=list(bill.values()),bound=bound,top_id=f.nv,encoding=8).clauses)
    with Solver(name='cadical195',bootstrap_with=f.clauses) as s:
        s.conf_budget(30000);v=s.solve_limited()
        print('collar',depth,'solver',v,flush=True)
        if v:
            true={x for x in s.get_model() if x>0}
            res=check_errors(n,lambda i,j:X[i*n+j] in true)
            if '--control' not in sys.argv:assert all(x[0]==81 for x in res)
            print('frames, persistent holes, example',res,'exact charge/budget',charge(n,dom,orig,X,ids,true),flush=True)
        if (v is False or v is None and '--drat' in sys.argv) and bound is None and not pattern:
            from .sector_gap_cover import verify
            ok=verify(f,f'repair_collar{n}_{depth}')
            if v is False:assert ok
if __name__=='__main__':test(int(sys.argv[1]),int(sys.argv[2]))
