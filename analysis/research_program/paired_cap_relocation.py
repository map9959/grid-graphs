"""Two unrestricted interior relocations from the covering or the rerouted cap."""
from itertools import combinations,product
from functools import lru_cache
from .rail_swap_uniform import geometry,expr,O,D,diag,cross,plus,close
from .neutral_rail_reroute import caprm,capins,cut,rect,edges

def run():
    inside,base=geometry()
    A=expr('t>=2');C=expr('t>=2 and i=29+42t and j=6+6t')
    U=expr('t>=2 and i=8+7t and j=17+21t')
    def capcell(u,v):
        return expr(f'i+{u[0]}=29+42t+{v[0]} and j+{u[1]}=6+6t+{v[1]}')
    @lru_cache(None)
    def Y(u):
        a=base(u)&A
        for v in caprm:a=a-capcell(u,v)
        for v in capins:a=a| (capcell(u,v)&A)
        return a
    def const(pos,pattern):
        if (pos-pattern).none():return True
        assert (pos&pattern).none()
        return False
    @lru_cache(None)
    def cap(v):return const(C,Y(v))
    def upper(u):
        i=f'(i+{u[0]})';j=f'(j+{u[1]})'
        return expr(f't>=2 and (({i}=0 and 0<={j}<32+42t) or '
                    f'({i}=2 and 2<={j}<=29+42t and {j}%3=2) or '
                    f'(3<={i}<8+7t and 3*{i}-4<={j}<39+42t-3*{i} and {j}%3=2))')
    # Different marked groups can share a forced component only through
    # contact at Manhattan distance <=2. The top bar/tooth set is sealed.
    top=upper(O);assert (top-Y(O)).none()
    for d in set.union(*(close(v) for v in cross)):
        assert (top&(Y(d)-upper(d))).none()
    # Even a chain of four edits (steps of length at most two) starting
    # on the rectangle is too low to add a mark within two of this group.
    assert expr('t>=2 and 29+42t+2-6<=7+7t+2').none()
    print('top teeth separated from other marks by distance >2; a connecting insertion is needed outside the cap cluster')

    xs=inside(O)&Y(O)
    lost={}
    for u in cross:
        z=xs
        for v in close(u)-{O}:z=z-Y(v)
        lost[u]=z
    z=xs
    for s in lost.values():z=z-s
    assert z.none()
    low=xs
    for a,b in combinations(D,2):low=low-(Y(a)&Y(b))
    joining=0
    catalogue=[((-1,0),(0,-1)),((2,-6),(3,-7)),((2,-3),(3,-4)),((2,4),(3,5))]
    for y in set.union(*(close(u) for u in cross))-{O}:
        z=(xs&inside(y))-Y(y)
        for d in diag:
            if plus(y,d)!=O:z=z-Y(plus(y,d))
        for u in set(cross)-close(y):z=z-lost[u]
        expected=expr('0=1')
        for a,b in catalogue:
            if plus(a,y)==b:expected=expected|(A&capcell(O,a))
        assert (expected-z).none() and (z-expected).none()
        assert (z&low).none()
        if z.none():continue
        # To make a new contact the inserted mark must be within two
        # grid steps of marks in BOTH of the formerly separate groups.
        reach=set.union(*(close(v) for v in close(y)))-{O}
        hits_top=expr('0=1');hits_other=expr('0=1')
        for v in reach:
            hits_top=hits_top|upper(v);hits_other=hits_other|(Y(v)-upper(v))
        if not (z&hits_top&hits_other).none():joining+=1
    print('remote covering one-for-one moves touching both marked groups: offset classes',joining)
    print('complete uniform covering single-swap catalogue (cap coordinates):',catalogue)
    assert joining==0
    print('covering cap, arbitrary interior site: no coverage-preserving diagonal-free one-for-one move gains a marked adjacency')

    def dist(u,v):return abs(u[0]-v[0])+abs(u[1]-v[1])
    # Cluster of the deletions breaking a specified cycle edge: at most
    # two removals and one insertion, so radius four suffices.
    W={plus(p,(a,b)) for p in rect for a,b in product(range(-4,5),repeat=2) if abs(a)+abs(b)<=4}
    R={u for u in W if cap(u) and const(C,inside(u))}
    good=[];noinsert=0
    for k in (1,2):
        for dels in combinations(sorted(R),k):
            rm=set(dels);on=lambda p:cap(p) and p not in rm
            if all(on(a) or on(b) for a,b in edges(rect)):continue
            lost={v for p in rm for v in close(p) if not any(on(q) for q in close(v))}
            if not lost:noinsert+=1;continue
            for z in sorted(set.intersection(*(close(v) for v in lost))):
                if cap(z) or not const(C,inside(z)):continue
                if any(on(plus(z,d)) for d in diag):continue
                if all(on(a) or on(b) or z in (a,b) for a,b in edges(rect)):continue
                old=sum(sum(cap(plus(p,d)) for d in D) for p in rm)-sum(dist(a,b)==1 for a,b in combinations(rm,2))
                good.append((dels,z,sum(on(plus(z,d)) for d in D)-old))
    assert noinsert==0 and good==[(((2,-6),),(3,-7),-1),(((2,4),),(3,5),-1)]
    print('covering cap cluster: zero insertions impossible; complete covering one-insertion list (deletions, insertion, adjacency change):',good)

    # If starting one step later with the tip at U, classify additions
    # according to whether the common cover of the two holes is restored.
    holes=[(1,2),(3,2)]
    assert set.intersection(*(close(v) for v in holes))=={cut}
    for h in holes:assert not any(cap(v) and v!=cut for v in close(h))
    def at_merger(p):return p==O or const(U,Y(p))
    merger=set()
    for s in (-1,1):
        cyc=[O,(0,s),(0,2*s),(1,2*s),(2,2*s),(2,s),(2,0),(1,0)]
        assert all(at_merger(a) or at_merger(b) for a,b in edges(cyc))
        merger.update(v for v in cyc if at_merger(v))
    private={p:[v for v in close(p) if not any(at_merger(q) for q in close(v)-{p})] for p in merger}
    assert [p for p,vs in private.items() if not vs]==[O]
    print('rerouted cap: common cover of both holes',cut,'; merger cycle marks',len(merger),'only mark without a private site',O)
def replay(n):
    """Physical check with flood-fill labels, independent of the affine tooth formula."""
    from .zipper_rails import build
    t=(n-35)//42;C=(n-6,6+6*t)
    X={(i,j) for i,row in enumerate(build(n)) for j,c in enumerate(row) if c=='#'}
    Y=(X-{plus(C,v) for v in caprm})|{plus(C,v) for v in capins}
    todo=[O];top={O}
    for u in todo:
        for v in close(u)-{u}:
            if 0<=min(v) and max(v)<n and v not in top and (u in Y or v in Y):
                top.add(v);todo.append(v)
    rad2=lambda u:set.union(*(close(v) for v in close(u)))
    bridge=paired=0;swaps=[]
    for x in Y:
        if min(x)==0 or max(x)==n-1:continue
        private={v for v in close(x) if close(v)&Y=={x}}
        assert private
        for z in set.intersection(*(close(v) for v in private))-Y:
            if min(z)<=0 or max(z)>=n-1 or any(plus(z,d) in Y and plus(z,d)!=x for d in diag):continue
            paired+=1;touch=(rad2(z)&Y)-{x};swaps.append((x,z))
            bridge+=bool(touch&top and touch-top)
    assert bridge==0
    print(n,'actual covering single replacements',paired,'possible new joins between old components',bridge)
    return sorted(swaps)
if __name__=='__main__':
    run()
    for n in (119,161,203):replay(n)
