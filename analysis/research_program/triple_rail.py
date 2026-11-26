"""Classify independent cap-cutter and upper-bridge edit clusters."""
from itertools import combinations,product
from collections import Counter,defaultdict
from functools import lru_cache
from .paired_cap_relocation import rect,edges,caprm,capins,cut,plus,close,D,diag,geometry,expr
from .zipper_rails import build
from .rail_swap_uniform import O,fn,Set,ptr,cp

def ball(r):
    return [(a,b) for a in range(-r,r+1) for b in range(-r+abs(a),r-abs(a)+1)]
B2=ball(2);B6=ball(6)
def around(p,V):return {plus(p,d) for d in V}
def touch(p,q):return abs(p[0]-q[0])+abs(p[1]-q[1])<=2
def connected(P):
    P=set(P);q=[P.pop()]
    for u in q:
        T={v for v in P if touch(u,v)};P-=T;q.extend(T)
    return not P
def delta(Y,rm,ins):
    def adjs(S):return sum(plus(p,d) in S for p in S for d in D[:2])
    return (sum(len((around(p,D)&Y)-rm) for p in ins)+adjs(ins)
            -sum(len(around(p,D)&Y) for p in rm)+adjs(rm))
def cap_options(Y):
    interior=lambda p:p[0]<5
    region=set.union(*(around(p,ball(8)) for p in rect))
    marked={p for p in region&Y if interior(p)}
    avail={p for p in region-Y if interior(p)}
    opts=defaultdict(set)
    edge_ends={frozenset({a,b}&Y) for a,b in edges(rect)}
    for E in edge_ends:
        if not E<=marked:continue
        for nr in range(len(E),4):
            for extra in combinations(marked-E,nr-len(E)):
                R=E|frozenset(extra)
                # Each deletion must have a private site covered by an addition.
                lost={v for p in R for v in close(p) if close(v)&Y<=R}
                if not lost:raise AssertionError('uncovered-site filter needs a private site')
                # First addition covers a chosen lost site. If the second
                # need not cover a lost site it can still participate nearby.
                v=min(lost)
                for a in close(v)&avail:
                    if not around(a,diag)&Y<=R:continue
                    left=lost-close(a)
                    for b in ([None] if not left else [])+list((avail&set.intersection(*(close(v) for v in left)) if left else avail)-{a}):
                        I=frozenset({a} if b is None else {a,b})
                        if b is not None and (b in around(a,diag) or not around(b,diag)&Y<=R):continue
                        if not connected(I|R):continue
                        if not any(not ({v,w}&(Y-R) or {v,w}&I) for v,w in edges(rect)):continue
                        opts[len(R),len(I),delta(Y,R,I)].add((R,I))
    return opts

def bridge_options(Y,top,interior,anchors):
    opts=defaultdict(set)
    for a in anchors:
        for b in [None]+[p for p in around(a,B6)-Y-{a} if interior(p)]:
            I=frozenset({a} if b is None else {a,b})
            if b in around(a,diag):continue
            req=set.union(*(around(p,diag)&Y for p in I))
            if len(req)>2 or not all(map(interior,req)):continue
            nearby={p for u in I for p in around(u,B2)&Y if interior(p)}
            for nr in range(len(req),3):
                for extra in combinations(nearby-req,nr-len(req)):
                    R=frozenset(req|set(extra))
                    if not connected(R|I):continue
                    if any(not ((close(v)&Y)-R or close(v)&I) for p in R for v in close(p)):continue
                    seen={a}
                    if b is not None and touch(a,b):seen.add(b)
                    touched=set.union(*((around(p,B2)&Y)-R for p in seen))
                    if not (touched&top and touched-top):continue
                    opts[len(R),len(I),delta(Y,R,I)].add((R,I))
    return opts

def raw(n):
    t=(n-35)//42;C=(n-6,6+6*t);r=build(n)
    Y={(i,j) for i,row in enumerate(r) for j,v in enumerate(row) if v=='#'}
    Y-=around(C,caprm);Y|=around(C,capins)
    top={p for p in Y if (p[0]==0 and p[1]<n-3) or (2<=p[0]<=7+7*t and p[1]%3==2 and
              (p[0]==2 and p[1]<=n-6 or p[0]>=3 and 3*p[0]-4<=p[1]<n+4-3*p[0]))}
    return C,Y,top

def shift_proof(base_t):
    """Every bridge neighborhood at a larger size is an actual translate."""
    inside,marks=geometry()
    add=fn('set_sum',ptr,ptr,ptr)
    def mink(a,b):return Set(add(cp(a.p),cp(b.p)))
    def expand(a,r):
        return mink(a,expr(f't=0 and {-r}<=i+j<={r} and {-r}<=i-j<={r}'))
    top=expr('((i=0 and 0<=j<32+42t) or (i=2 and 2<=j<=29+42t and j%3=2) or '
             '(3<=i<8+7t and 3*i-4<=j<39+42t-3*i and j%3=2))')
    Y=marks(O)
    for a,b in caprm:Y=Y-expr(f'i=29+42t+{a} and j=6+6t+{b}')
    for a,b in capins:Y=Y|expr(f'i=29+42t+{a} and j=6+6t+{b}')
    anchors=(inside(O)&expand(top,2)&expand(Y-top,4))-Y
    bad=anchors&expr(f't>{base_t}')
    for a,b in ((0,0),(0,42),(7,21)):
        step=expr(f't=1 and i={a} and j={b}');diff=expr('0=1')
        for V in (Y,top,inside(O)):
            old=mink(V,step);diff=diff|(V-old)|(old-V)
        bad=bad&expand(diff,10)
    print('every bridge halo at t>',base_t,'reduces by 42:',bad.none(),flush=True)
    return bad.none()

def remote_contractions():
    """An independent 2-out,1-in edit anywhere: both deletions have private sites."""
    inside,base=geometry()
    @lru_cache(None)
    def Y(u):
        v=base(u)
        for a,b in caprm:v=v-expr(f'i+{u[0]}=29+42t+{a} and j+{u[1]}=6+6t+{b}')
        for a,b in capins:v=v|expr(f'i+{u[0]}=29+42t+{a} and j+{u[1]}=6+6t+{b}')
        return v
    start=(inside(O)&expr('t>=2'))-Y(O);survive=[]
    for a,b in combinations(set(B2)-{O},2):
        rm={a,b}
        A=start&Y(a)&Y(b)&inside(a)&inside(b)
        for d in diag:
            if d not in rm:A=A-Y(d)
        for u in (close(a)|close(b))-close(O):
            witness=expr('0=1')
            for v in close(u)-rm:witness=witness|Y(v)
            A=A&witness
        if not A.none():survive.append((a,b))
    print('covering 2-out/1-in displacement pairs anywhere:',survive,flush=True)
    return survive

def rerouted(n):
    C,Y,top=raw(n);t=(n-35)//42;U=(8+7*t,17+21*t)
    Z=(Y-{plus(C,cut)})|{U}
    holes=around(C,{(1,2),(3,2)})
    cycles=[[(0,0),(0,s),(0,2*s),(1,2*s),(2,2*s),(2,s),(2,0),(1,0)] for s in (-1,1)]
    cycles=[[plus(U,v) for v in cyc] for cyc in cycles]
    def interior(p):return min(p)>0 and max(p)<n-1
    # Only positions within two of U could lose their old private sites
    # when U is inserted, and deleting cut cannot cause that effect.
    assert all(any(close(v)&Z=={p} for v in close(p)) for p in (around(U,B2)&Z)-{U})
    def profiles(options,cap):
        counts=Counter()
        for I in options:
            if any(not interior(v) or v in Z for v in I):continue
            if any(b in around(a,diag) for a,b in combinations(I,2)):continue
            avail=set.union(*(around(v,B2)&Z for v in I))-{U}
            req=set.union(*(around(v,diag)&Z for v in I))
            if not req<=avail:continue
            for nr in range(len(req),4):
                for extra in combinations(avail-req,nr-len(req)):
                    R=req|set(extra)
                    if not all(map(interior,R)):continue
                    if any(not ((close(v)&Z)-R or close(v)&I) for p in R for v in close(p)):continue
                    if not cap and any(all(({a,b}&Z)-R or {a,b}&I for a,b in edges(c)) for c in cycles):continue
                    counts[nr,len(I),delta(Z,R,I)]+=1
        return counts
    h1,h2=holes
    capopts={frozenset((a,b)) for a,b in product(close(h1),close(h2)) if a!=b and plus(C,cut) not in (a,b)}
    # A marked vertex on a broken square is deleted, hence the only
    # non-cap insertion must be within two of it. U is retained.
    other=set.union(*(around(v,B2) for v in set(cycles[0])&Z if v!=U))
    cp=profiles(capopts,True);bp=profiles([{a} for a in other],False)
    hits=sum(v*bp[3-r,3-i,-d] for (r,i,d),v in cp.items())
    print(n,'two private holes, tip retained: cap profiles',dict(sorted(cp.items())),
          'both 8-cycles broken',dict(sorted(bp.items())),'compatible triples',hits,flush=True)
    return cp,bp,hits

def check():
    # Cap cluster has at most five edits, hence is inside the radius-eight
    # enlargement of the rectangle. Include two more layers for the
    # coverage and run tests. For the merger rerouting the furthest
    # affected original bit is within 2+2+2+2+2 of the new tip.
    C,Y,T=raw(119);inside,base=geometry()
    caparea=set.union(*(around(p,ball(10)) for p in rect))
    for aff,origin,area in [('i=29+42t and j=6+6t',C,caparea),
                            ('i=8+7t and j=17+21t',(22,59),ball(10))]:
        at=expr('t>=2 and '+aff);board=build(119)
        for p in area:
            i,j=plus(origin,p);marked=0<=i<119 and 0<=j<119 and board[i][j]=='#'
            assert (at-base(p) if marked else at&base(p)).none()
            ok=0<i<118 and 0<j<118
            assert (at-inside(p) if ok else at&inside(p)).none()
    cap=cap_options({p for p in caparea if plus(C,p) in Y})
    print('cap cluster (removed,inserted,adjacency change):',sorted((k,len(v)) for k,v in cap.items()),flush=True)
    assert expr('t>=2 and 29+42t+2-10<=7+7t+2').none()
    assert not remote_contractions()
    assert shift_proof(5)
    bridge=set()
    for t in range(2,6):
        n=35+42*t;C,Y,top=raw(n)
        inside_board=lambda p:0<min(p) and max(p)<n-1
        reach=set.union(*(around(p,B2) for p in top))
        A={p for p in reach-Y if inside_board(p) and (around(p,ball(4))&Y)-top}
        prof=bridge_options(Y,top,inside_board,A);bridge.update(prof)
        print(n,'bridge cluster profiles',sorted(prof),flush=True)
    # Even when not connected to one another, leftover edits must
    # satisfy their own coverage conditions, independently of both clusters.
    for a,b in product(cap,bridge):
        r=3-a[0]-b[0];i=3-a[1]-b[1];delta_needed=-a[2]-b[2]
        if r<0 or i<0:continue
        if i==0 and r>0:continue  # every deleted site has a private site
        if (r,i)==(2,1):continue  # unrestricted contraction test
        assert (r,i)==(0,0) and delta_needed!=0,(a,b,r,i,delta_needed)
    print('no compatible coverage-preserving cap/bridge/remaining allocation at (3,3,0)')
    for n in (119,161,203):assert rerouted(n)[2]==0
if __name__=='__main__':check()
