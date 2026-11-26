"""Which crop leftovers actually change the rank of an end-band replacement?"""
from .collar_vacancies import shadows,comb
from .end_band_rank import refill
from .comb_cap_transfer import construct
from .sparse_component_exchange import Forest
from .extend_forest_28 import verify
from .wired_crop_exchange import ring
from .end_band_obstruction import wrapped

def leftovers(rows):
    n=len(rows);c=[s[6:-6] for s in rows[6:-6]]
    (_,_,_,_),paid=shadows(rows,2,c,True)
    U={(i+d,j+d) for d in (4,5) for i,j in ring(n-2*d) if rows[i+d][j+d]=='#'}-paid
    marks=lambda r:sum(s.count('#') for s in r)
    return U,marks(rows)-marks(c)-len(paid)

def edges(n):
    for y in range(n):
        for x in range(n):
            if x+1<n:yield (y,x),(y,x+1)
            if y+1<n:yield (y,x),(y+1,x)

def quotient(rows,ys,U,l=0,r=None,centers=None,check_subsets=False):
    n=len(rows)
    if r is None:r=n-1
    if centers is None:centers=range(0,n,3)
    data={};_,price=refill(rows,ys,l,r,centers,ledger=data)
    D=data['tiles'];Z=data['clipped']
    # A remote donor can neither change port eligibility nor undo a
    # compulsory deletion. Edges with permanent owners stay in the base.
    U={p for p in U-Z if all(abs(p[0]-y)>2 for y in ys)}
    M={(i,j) for i,row in enumerate(rows) for j,c in enumerate(row) if c=='#'}-Z
    F=Forest(n);es=[]
    for p,q in edges(n):
        if p in D or q in D:continue
        owners={p,q}&M
        if owners-U:assert F.join(p,q)
        elif owners:es.append((p,q,owners))
    for p,q in data['compulsory']:assert F.join(p,q)
    high=sum(F.join(p,q) for p,q in data['optional'])
    es=[(F.root(p),F.root(q),o) for p,q,o in es]
    def beta(deleted):
        par={}
        def rt(i):
            while i in par:i=par[i]
            return i
        b=0
        for p,q,o in es:
            if o<=deleted:continue
            p,q=rt(p),rt(q)
            if p==q:b+=1
            else:par[p]=q
        return b
    total=beta(set());assert high-price[3]==total
    if check_subsets:
        from itertools import combinations
        for size in range(len(U)+1):
            for subset in combinations(U,size):
                S=set(subset);x=list(map(list,rows))
                for i,j in S|Z:x[i][j]='.'
                out,p2=refill([''.join(s) for s in x],ys,l,r,centers)
                assert p2[5]==0 and p2[3]-price[3]==total-beta(S)
                verify(out)
        print(2**len(U),'subsets: quotient ranks matched complete physical refills')
    # Remove a profitable single donor until none remains. The exact
    # benefit for ANY suggested set S is beta(empty)-beta(S)-|S|.
    S=set();cur=total
    while U-S:
        val,v=min((beta(S|{v}),v) for v in U-S)
        if cur-val<=1:break
        S.add(v);cur=val
    if S:
        x=list(map(list,rows))
        for y,j in S:x[y][j]='.'
        x=[''.join(s) for s in x]
        # Keep the initial compulsory cut decisions; without preclipping
        # a fresh repair may choose a different basis.
        x=list(map(list,x))
        for y,j in Z:x[y][j]='.'
        x=[''.join(s) for s in x]
        out,p2=refill(x,ys,l,r,centers)
        assert not p2[5] and p2[3]-price[3]==total-cur
        verify(out)
    return price,len(U),total,total-cur-len(S)

def patched(n,h):
    # Graft one constant square from a tangential collar into the north-west
    # corner of the comb. Two blank lines separate forced supports.
    rows=list(map(list,construct(n,4)))
    for y in range(h+2):
        for x in range(h+2):rows[y][x]='.'
    for i in range(0,h,3):
        for j in range(i,h):
            rows[i][j]=rows[j][i]='#'
        if i+1<h:rows[i][i+1]='.'
    return [''.join(s) for s in rows]

def fork(n):
    rows=list(map(list,construct(n,4)));x0=3*(n//6)
    for i in range(17):
        for j in range(x0-11,x0+12):rows[i][j]='.'
    teeth=(x0-6,x0,x0+6)
    for x in range(x0-8,x0+9):
        if all(abs(x-j)!=1 for j in teeth):rows[5][x]='#'
        rows[12][x]='#'
    for x in teeth:rows[6][x]='#'
    return [''.join(s) for s in rows]

def occupied_fringe(n):
    rows=list(map(list,wrapped(n)))
    for side in range(4):
        def rc(y,x):
            for _ in range(side):y,x=x,n-1-y
            return y,x
        for y,offset in ((2,0),(5,-24),(5,-12),(5,12),(5,24)):
            x=n//2+offset;i,j=rc(y,x);rows[i][j]='#'
            for dx in (-1,1,2):
                i,j=rc(y+1,x+dx);rows[i][j]='.'
    return [''.join(s) for s in rows]

def locked_fringe(n,teeth=7):
    rows=list(map(list,wrapped(n)))
    for side in range(4):
        def put(y,x,c):
            for _ in range(side):y,x=x,n-1-y
            rows[y][x]=c
        x0=3*(n//6)+1
        X={x0+i for i in (-9,-6,-3)}
        assert teeth>=7 and teeth%2 and min(x0,n-1-x0)>=3*(teeth//2)+20
        Y={x0+3*i for i in range(-(teeth//2),teeth//2+1)}
        for h,sites in ((2,X),(5,Y)):
            for x in sites:
                put(h,x,'#')
                for j in (-1,1,2,4):put(h+1,x+j,'.')
                for j in (0,3):put(h+2,x+j,'#')
        for x in Y:
            for j in (0,3):put(9,x+j,'.')
    return [''.join(s) for s in rows]

def boundary_ceiling(rows,h):
    c=[s[h:-h] for s in rows[h:-h]];m=len(c)
    # Frozen interior, but arbitrary deletions AND insertions on the
    # smaller rim. Every originally empty site with a marked interior
    # diagonal is unavailable in every feasible replacement.
    R=set(ring(m));return sum(c[y][x]=='.' and not any(
        0<=i<m and 0<=j<m and (i,j) not in R and c[i][j]=='#'
        for i in (y-1,y+1) for j in (x-1,x+1)) for y,x in R)

def rail_ceiling(rows,ys):
    """Any exterior deletions paid at one per mark; no crop assumptions."""
    n=len(rows);gain=0
    assert abs(ys[1]-ys[0])>6
    for y in ys:
        eligible={}
        for x in range(0,n,3):
            eligible[x]=sum(not(0<=i<n and any(rows[i][j]=='#' for j in (x-1,x+1) if 0<=j<n))
                            for i in (y-2,y+2))
        gain+=sum(1+v for v in eligible.values())-sum(rows[i].count('#') for i in (y-1,y,y+1))
        if not 3<=y<n-3:continue
        for x in range(0,n-3,3):
            if eligible[x]==eligible[x+3]==2 and all(rows[i][j]=='#' for i in (y-3,y+3) for j in range(x,x+4)):
                gain-=1
    return gain

def audit():
    small=['.'*31 for _ in range(31)];sm=list(map(list,small))
    for j in range(4,27):
        if j not in (8,10,14,16,20,22):sm[5][j]='#'
        sm[12][j]='#'
    for j in (9,15,21):sm[6][j]='#'
    quotient([''.join(s) for s in sm],(9,24),{(5,j) for j in (4,5,9,15,21)},check_subsets=True)
    # One donor with two independent return paths: exactly pays a losing cut.
    n=163;f=fork(n);cx=3*(n//6);r=list(map(list,patched(n,81)))
    for y in range(17):r[y][79:102]=f[y][cx-11:cx+12]
    r=verify([''.join(s) for s in r],True);U,lost=leftovers(r)
    assert (5,90) in U
    p,_,beta,bonus=quotient(r,(9,n-10),{(5,90)})
    assert (p[-1],beta,bonus)==(-1,2,1) and lost>comb(n)-comb(n-12)
    print('fork: physical tree',verify(r),'crop loss/budget',lost,comb(n)-comb(n-12),
          'end gain, released rank, gain after fee and repair',p[-1],beta,p[-1]+bonus)
    plain=occupied_fringe(103);assert verify(plain,True)==plain
    _,loss=leftovers(plain);gain,repaired=lateral_recovery(plain,6)
    assert gain==16 and loss-gain<=comb(103)-comb(91)
    print('occupied shadows without interior locks: crop loss',loss,'lateral gains',gain,'tree',verify(repaired))
    # Replay the actual tree and use all its full vertices for both tests.
    r=locked_fringe(103);n=len(r);assert verify(r,True)==r
    U,lost=leftovers(r)
    print('locked fringe: physical tree',verify(r),'comb',comb(n),'leftovers',len(U))
    for h in (3,6):
        raw=sum(s.count('#') for s in r)-sum(s[h:-h].count('#') for s in r[h:-h])
        b=boundary_ceiling(r,h);assert raw-b>comb(n)-comb(n-2*h)
        print('peel',h,'removed, maximum boundary gain ceiling, budget',raw,b,comb(n)-comb(n-2*h))
    for board in (r,[''.join(z) for z in zip(*r)]):
        V,_=leftovers(board)
        assert any(board[y][3]==board[y+1][3]=='.' for y in range(10,n-11))
        pairs=[(a,b) for a in range(1,10) for b in range(n-10,n-1)]
        ceilings=[rail_ceiling(board,z) for z in pairs]
        maxrank=max(ceiling(board,z,V) for z in pairs)
        assert maxrank<0 and max(ceilings)<0
        print(len(pairs),'cut pairs, best cographic ceiling',maxrank,
              'best arbitrary-paid-deletion rail ceiling',max(ceilings))

def lateral_recovery(rows,h):
    """Offer either flanking vacancy of an occupied straight shadow.

    Work in the crop's actual forest. A successful promotion owns at
    most two previously absent edges, since it touches the old shadow.
    """
    n=len(rows);c=[list(s[h:-h]) for s in rows[h:-h]];m=len(c)
    F=Forest(m)
    for p,q in edges(m):
        if '#' in (c[p[0]][p[1]],c[q[0]][q[1]]):assert F.join(p,q)
    before=sum(s.count('#') for s in c);used=set()
    for side in range(4):
        def rot(y,x,k):
            for _ in range(side):y,x=x,k-1-y
            return y,x
        for x in range(1,m-1):
            sy,sx=rot(h-1,h+x,n);ty,tx=rot(0,x,m)
            if rows[sy][sx]!='#' or c[ty][tx]!='#':continue
            for j in (x-1,x+1):
                v=rot(0,j,m);y,z=v
                if c[y][z]=='#':continue
                other=[p for p in ((y-1,z),(y+1,z),(y,z-1),(y,z+1)) if
                       0<=p[0]<m and 0<=p[1]<m and c[p[0]][p[1]]=='.']
                parts=[F.root(p) for p in [v,*other]]
                if len(parts)!=len(set(parts)):continue
                for p in other:assert F.join(v,p)
                c[y][z]='#';used.add((sy,sx));break
    c=[''.join(s) for s in c];assert sum(s.count('#') for s in c)==before+len(used)
    return len(used),c

def ceiling(rows,ys,U,l=0,r=None,bad_only=False):
    """Optimistic price even with arbitrary deletions of leftover marks.

    Any compulsory edge rejected after such deletions lies on an original
    compulsory cycle. Relax every such edge and its backing owner.
    """
    n=len(rows);r=n-1 if r is None else r
    D={(i,x) for y in ys for c in range(l+(3-l%3)%3,r+1,3)
       if not bad_only or any((rows[y][j]=='#')!=(j==c) for j in range(max(l,c-1),min(r,c+1)+1))
       for i in (y-1,y,y+1) for x in range(max(l,c-1),min(r,c+1)+1)}
    M={(y,x) for y,row in enumerate(rows) for x,v in enumerate(row) if v=='#'}
    pp=[((y,c),(y+2*s,c)) for y in ys for c in range(0,n,3) if (y,c) in D for s in (-1,1)]
    def base(omit):
        F=Forest(n);keep=M-omit
        for p,q in edges(n):
            if p not in D and q not in D and (p in keep or q in keep):assert F.join(p,q)
        return F
    F=base(set());comp=[(p,q) for p,q in pp if q in M]
    # A tooth with only one compulsory incidence cannot be on a cycle.
    # Find nonbridges in the much smaller compulsory multigraph.
    arcs=[(F.root(p),F.root(q)) for p,q in comp]
    def oncycle(i):
        u,v=arcs[i];adj={}
        for j,(a,b) in enumerate(arcs):
            if i!=j:adj.setdefault(a,[]).append(b);adj.setdefault(b,[]).append(a)
        seen={u};stack=[u]
        while stack:
            for x in adj.get(stack.pop(),()):
                if x not in seen:stack.append(x);seen.add(x)
        return v in seen
    V=(U-D)|{q for i,(_,q) in enumerate(comp) if oncycle(i)}
    F=base(V)
    donor_edges=[]
    for p,q in edges(n):
        if p in D or q in D:continue
        owners={p,q}&M
        if owners and owners<=V:donor_edges.append((p,q,owners))
    free=rank=0;coupons=set()
    for p,(i,x) in pp:
        if 0<=i<n and any((i,j) in M for j in (x-1,x+1)):
            block={(i,j) for j in (x-1,x+1)}&M
            if block<=V:coupons.add(min(block))
            continue
        if not 0<=i<n:free+=1
        else:rank+=F.join(p,(i,x))
    # Contract all optional edges also. Gain in optional rank when
    # removing remote edges L is exactly their cographic rank.
    es=[(F.root(p),F.root(q),o) for p,q,o in donor_edges]
    def nullity(skip):
        par={};v=0
        def rt(i):
            while i in par:i=par[i]
            return i
        for p,q,o in es:
            if skip in o:continue
            p,q=rt(p),rt(q)
            if p==q:v+=1
            else:par[p]=q
        return v
    beta=nullity(None)
    extra=min(beta,sum(max(0,beta-nullity(u)-int(u not in coupons)) for u in V))
    return len(pp)//2+free+rank-beta+extra-len(D&M)

if __name__=='__main__':audit()
