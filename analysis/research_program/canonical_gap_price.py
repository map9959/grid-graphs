"""Share the seven-gap sector budget across disjoint canonical side windows."""
from itertools import product
from .sector_gap_cover import data,generate,gaps,verify

def target(n):
    k=n//3;assert n%9==4
    return 3*k*k+(16*k-7)//3

def exact_gaps(f,X,edges,n,z):
    from pysat.card import CardEnc
    from pysat.formula import IDPool
    pool=IDPool(start_from=f.nv+1);gs=[]
    for (i,j),(u,v) in edges:
        a,b=X[i*n+j],X[u*n+v];c=pool.id();gs.append(c)
        f.extend([[-c,-a],[-c,-b],[a,b,c]])
    if z:f.extend(CardEnc.atleast(gs,z,vpool=pool).clauses)
    if z<len(gs):f.extend(CardEnc.atmost(gs,z,vpool=pool).clauses)

def make(n,t,tables,D,edges):
    from .wired_crop_exchange import ring
    r=ring(n);bill={};f,X=generate(n,t,D,False,tables,bill=bill)
    for j,(y,x) in enumerate(r):
        near=min(max(y,x),max(n-1-y,x),max(y,n-1-x),max(n-1-y,n-1-x))
        tri=[r[j-1],r[j],r[(j+1)%len(r)]]
        if near>=2 and all(v in D for v in tri):
            a,b,c=(X[i*n+k] for i,k in tri);f.append([-a,b,-c])
    return f,X,bill

def run_rules(f,X,n,D,no_chord=False):
    from .patch_square import trans
    for side in range(4):
        for j in range(2,n-3):
            def pts(offsets):return [trans(y,j+x,n,side) for y,x in offsets]
            for step in (-1,1):
                sites=pts([(0,i*step) for i in (-2,-1,0,1,2)])
                if all(v in D for v in sites):
                    a,b,c,d,e=[X[i*n+x] for i,x in sites]
                    f.append([-a,-b,c,d,e]) # ##... cannot start a long vacancy run
            if no_chord:
                sites=pts([(0,k) for k in (-2,-1,0,1,2,3)]+[(2,0),(2,1)])
                if all(v in D for v in sites):
                    a,b,c,d,e,g,u,v=[X[i*n+x] for i,x in sites]
                    for donor in (u,v):f.append([-a,-b,c,d,-e,-g,donor])

def prices(n,tag,D,edges,levels,tables,limit=6000):
    from pysat.solvers import Solver
    from pysat.formula import CNF
    from pysat.pb import PBEnc
    f,X,bill=make(n,target(n),tables,D,edges);ans=[]
    for z in levels:
        b=CNF(from_clauses=f.clauses);exact_gaps(b,X,edges,n,z)
        low,high=0,33
        while low<high:
            m=(low+high)//2
            pb=PBEnc.atmost(lits=list(bill),weights=list(bill.values()),bound=m,top_id=b.nv,encoding=8)
            with Solver(name='cadical195',bootstrap_with=b.clauses) as s:
                s.append_formula(pb.clauses);s.conf_budget(limit);v=s.solve_limited()
            if v is False:low=m+1
            else:high=m
        if low:
            b.extend(PBEnc.atmost(lits=list(bill),weights=list(bill.values()),bound=low-1,top_id=b.nv,encoding=8).clauses)
            if not verify(b,f'canonical_price_{n}_{tag}_{z}_{low}'):low=0
        ans.append(low);print(tag,z,'verified lower',low,flush=True)
    return ans

def corners(n,tables,rot):
    from .patch_square import trans
    D={trans(i,j,n,rot) for i,j in product(range(44),repeat=2)
       if min(i,j)<6 or max(i,j)<20}
    edges=[(trans(*a,n,rot),trans(*b,n,rot)) for j in range(38)
           for a,b in (((0,j),(0,j+1)),((j,0),(j+1,0)))]
    return prices(n,f'corner38_{rot}',D,edges,range(8),tables)

def patch_prices(n,tables,rot,asks):
    from pysat.formula import CNF
    from pysat.pb import PBEnc
    from .patch_square import trans
    from .rim_patch_dominance import forbid
    D={trans(i,j,n,rot) for i,j in product(range(44),repeat=2) if min(i,j)<6 or max(i,j)<20}
    edges=[(trans(*a,n,rot),trans(*b,n,rot)) for j in range(38)
           for a,b in (((0,j),(0,j+1)),((j,0),(j+1,0)))]
    f,X,bill=make(n,target(n),tables,D,edges);run_rules(f,X,n,D)
    for h,w in ((3,5),(4,4)):forbid(f,X,n,D,h,w)
    validated={}
    for z,price in asks:
        b=CNF(from_clauses=f.clauses);exact_gaps(b,X,edges,n,z)
        if price<=64:b.extend(PBEnc.atmost(lits=list(bill),weights=list(bill.values()),bound=price-1,top_id=b.nv,encoding=8).clauses)
        ok=verify(b,f'canonical_patch_price_{n}_{rot}_{z}_{price}')
        print('corner',rot,z,'price',price,'verified',ok,flush=True)
        if ok:validated[z]=price
    return validated

def seven(n,tables):
    from itertools import combinations_with_replacement
    root=patch_prices(n,tables,0,[(7,65),(6,64),(5,61),(4,59),(3,39),(2,22)])
    other=patch_prices(n,tables,1,[(1,2),(2,22),(3,30)])
    cases=[p for p in combinations_with_replacement(range(8),4) if sum(p)==7]
    bills=[root.get(p[-1],0)+sum(other.get(z,0) for z in p[:-1]) for p in cases]
    print('seven-gap corner bills',list(zip(cases,bills)),flush=True)
    assert min(bills)>64

def localize(n,tables):
    from .patch_square import trans
    from pysat.pb import PBEnc
    t=target(n)
    a=set(product(range(5),range(28,44)));ae=[((0,j),(0,j+1)) for j in range(33,38)]
    f,X,bill=make(n,t,tables,a,ae);gaps(f,X,ae,n,1)
    f.extend(PBEnc.atmost(lits=list(bill),weights=list(bill.values()),bound=26,top_id=f.nv,encoding=8).clauses)
    assert verify(f,f'canonical_flat_one_{n}')
    b=set(product(range(5),range(30,62)));be=[((0,j),(0,j+1)) for j in range(35,56)]
    f,X,_=make(n,t,tables,b,be);gaps(f,X,be,n,3)
    assert verify(f,f'canonical_flat_three_{n}')
    for rot in (0,1):
        D={trans(i,j,n,rot) for i,j in product(range(29),repeat=2) if min(i,j)<6 or max(i,j)<13}
        edges=[(trans(*a,n,rot),trans(*b,n,rot)) for j in range(24) for a,b in (((0,j),(0,j+1)),((j,0),(j+1,0)))]
        f,X,bill=make(n,t,tables,D,edges);gaps(f,X,edges,n,2)
        f.extend(PBEnc.atmost(lits=list(bill),weights=list(bill.values()),bound=5,top_id=f.nv,encoding=8).clauses)
        assert verify(f,f'canonical_near_two_{n}_{rot}')
    def windows(D,edges):
        ds=[]
        # Compare the full eight-image coordinate labels (including
        # both signed diagonals) for every possible charged atom.
        for sh in range(-3*n,3*n+1,3):
            if any(not(0<=x+sh<n-2) for _,x in D):continue
            if all(tables[0](i,x,j)==tables[0](i,x+sh,j) for i,x in D for j in (0,1)):
                ds.append((frozenset(x+sh for _,x in D),set(p[1]+sh for p,_ in edges)))
        return ds
    one=windows(a,ae);three=windows(b,be);flat=range(24,n-1-24)
    from itertools import combinations
    covers={j:[D for D,E in one if j in E] for j in flat}
    assert all(covers.values())
    for j in range(38,n-1-38):
        assert any(min(D)>=29 and max(D)<n-29 for D in covers[j])
    for x,y,z in combinations(flat,3):
        assert any({x,y,z}<=E for _,E in three) or any(not A&B for A in covers[x] for B in covers[z])
    print('canonical seven-gap branch: at most two flat gaps; every gap within 38 bonds of a corner',flush=True)

if __name__=='__main__':
    import sys
    assert all(f in sys.argv for f in ['--deep','--rim-gaps=7'])
    assert ('--bins=64' if '--patch-price' in sys.argv or '--seven' in sys.argv else '--bins=32') in sys.argv
    n=next((int(a.split('=')[1]) for a in sys.argv if a.startswith('--side=')),103)
    tables=data(n,target(n))
    # Five paid central bonds; windows that are summed must have
    # disjoint charged atoms. These figures alone do not cover corners.
    if '--seven' in sys.argv:seven(n,tables)
    elif '--patch-price' in sys.argv:
        asks=[tuple(map(int,s.split(':'))) for s in sys.argv if ':' in s]
        rot=next((int(s.split('=')[1]) for s in sys.argv if s.startswith('--turn=')),0)
        patch_prices(n,tables,rot,asks)
    elif '--localize' in sys.argv:localize(n,tables)
    elif '--corners' in sys.argv:
        for s in (0,1):print('corner tariff',s,corners(n,tables,s),flush=True)
    elif '--shell' in sys.argv:
        from .wired_crop_exchange import ring
        r=ring(n);D={(i,j) for i,j in product(range(n),repeat=2) if min(i,j,n-1-i,n-1-j)<5}
        edges=list(zip(r,r[1:]+r[:1]));f,X,_=make(n,target(n),tables,D,edges);exact_gaps(f,X,edges,n,7)
        print('canonical seven-gap shell excluded?',verify(f,'canonical_shell7'),flush=True)
    else:
        D=set(product(range(5),range(28,44)));edges=[((0,j),(0,j+1)) for j in range(33,38)]
        prices(n,'flat',D,edges,range(6),tables)
