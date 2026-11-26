"""Price both uses of the same interface word against the exact port forests."""
from .core_boundary_envelope import path,extend
from .arbitrary_collar_transfer import marks,engine
from .extend_forest_28 import verify
from .sparse_component_exchange import Forest,graph
from .wired_crop_exchange import ring
from .collar_vacancies import comb
from itertools import product

def joint(rows,d):
    n=len(rows);s=n-2*d
    outer=[ ''.join(v if min(y,x,n-1-y,n-1-x)<d else '.' for x,v in enumerate(row))
            for y,row in enumerate(rows)]
    F=graph(outer,set());lab=[];old=[];ports=[];rep=[]
    for i,j in ring(s):
        y,x=i+d,j+d;norm=[]
        # Split a corner into consecutive equal-bit tokens in cyclic order.
        if i==0 and j==0:norm=[(y,x-1),(y-1,x)]
        else:
            if i==0:norm.append((y-1,x))
            if j==s-1:norm.append((y,x+1))
            if i==s-1:norm.append((y+1,x))
            if j==0:norm.append((y,x-1))
        for k,(a,b) in enumerate(norm):
            lab.append(F.root((a,b)));old.append(outer[a][b]=='#');ports.append((y,x));rep.append(k>0)
    # Compute labels in the INDUCED exterior, without phantom paths via
    # a blank corner touched by two exterior marks. Two such marks would
    # be diagonal, so this shortcut gives precisely the induced partition.
    sites=ring(s);pairs=[]
    for j,p in enumerate(sites):
        if all(t in (0,s-1) for t in p):
            pairs.append([ports.index((a+d,b+d)) for a,b in (sites[j-1],sites[(j+1)%len(sites)])])
    # The two arms at each inside corner also see the same blank
    # vertex of the erased core. At least one of them must be unmarked.
    eo,w=max(path(lab,old,True,repeat=rep,forbidden=frozenset(f)) for f in product(*pairs))
    out=list(map(list,outer))
    for i,(y,x) in enumerate(ports):
        if w>>i&1:out[y][x]='#'
    v=verify([''.join(r) for r in out]);assert v[0]==marks(outer)+eo
    c=[r[d+1:-d-1] for r in rows[d+1:-d-1]]
    ei,t=extend(c,4)
    b=sum(rows[i+d][j+d]=='#' for i,j in ring(s))
    assert eo>=b and ei>=b
    return b,eo,ei,v,t

def upper(n):
    k=n//3
    if n%3==0:return 3*k*k+3*k-2
    if n%3==2:return 3*k*k+7*k-(k-5)//7-int(n%42==35)
    return 3*k*k+5*k+(k-5)//3

def universal(n,d):
    # width-nine constant 33.5 per corner; see the 16..19 bases
    assert n>=103
    return {3:8*n-40,8:14*n-118,9:16*n-170}[d]

def estimate(rows,d):
    n=len(rows);b,eo,ei,_,_=joint(rows,d);s=n-2*d;U=universal(n,d)
    cap=min(U,sum(engine(('outer',d+1,d),rows)[0]))
    return (b,eo,ei,U+upper(s)-(eo+ei-b),cap+upper(s)-(eo+ei-b))

def punctures(n,double=False):
    """A connected ninth ring with complementary (or double) component returns."""
    from .end_band_obstruction import wrapped
    r=list(map(list,wrapped(n)))
    # Put the one missing bond across a corner, not inside a straight arm.
    r[9][9]='.';r[9][11]='#'
    def at(s,y,x):
        for _ in range(s):y,x=x,n-1-y
        return y,x
    def put(s,y,x,c):i,j=at(s,y,x);r[i][j]=c
    def return_at(s,y,x):
        bar=6 if y==7 else 12
        for dx in (-1,1):put(s,bar,x+dx,'.')
        put(s,y,x,'#')
    # One anchor per return bar, to the same marked side-9 path.
    return_at(0,7,18);return_at(0,11,24)
    for s in range(4):
        for j,x in enumerate(range(32,n-28,9)):
            put(s,9,x,'.')
            if double or j%3==0:return_at(s,7,x)
            if double or j%3==1:return_at(s,11,x)
    return [''.join(z) for z in r]

def dense_cap(n):
    # Corner prices exclude the already counted pitch slices. Side
    # prices are measured relative to three marks per slice.
    dp={0:0}
    for prices in ([36,36,37,38,38,39],[-4,-2,-1,0,0,0])*4:
        nd={}
        for k,v in dp.items():
            for rank,cost in enumerate(prices):
                if k+rank<=23:nd[k+rank]=max(nd.get(k+rank,-1000),v+cost)
        dp=nd
    assert max(dp.values())==151
    return 12*(n-20)+max(dp.values())

def free_ended(n,B,core_gain):
    # Gap four, first/last depth-eight bits blank, other end bits free.
    return upper(n-18)+12*n-72+(184-B)//9-core_gain

def dense_transfer(r):
    n=len(r);m=n-20;bad=0;spaced=True;ranks=[];corner_r=[]
    for _ in range(4):
        assert all(r[y][j]==('#' if y in (0,3,6) else '.') for j in (10,n-11) for y in range(9))
        holes=[x for x in range(10,n-10) if r[9][x]=='.']
        assert all(b-a>=3 for a,b in zip(holes,holes[1:]))
        spaced &= all(b-a>=4 for a,b in zip(holes,holes[1:]))
        bad+=sum(any((r[y][x]=='#')!=(y in (0,3,6)) for y in range(8)) for x in range(10,n-10))
        # Independent physical reconstruction of each piece with its
        # terminal identifications. No quotient in these grid unions.
        def piece(D,term,omit=set()):
            F=Forest(n)
            for y,x in D:
                for i,j in ((y+1,x),(y,x+1)):
                    if (i,j) in D and (((y,x) not in omit and r[y][x]=='#') or
                                         ((i,j) not in omit and r[i][j]=='#')):
                        assert F.join((y,x),(i,j))
            return 6-len({F.root(t) for t in term})
        D={(y,x) for y in range(10) for x in range(10,n-10)}
        rank=piece(D,[(y,x) for y in (0,3,6) for x in (10,n-11)])
        arms=sum(r[y][x]=='#' for y,x in D if y<9)
        assert arms<=3*m+[-4,-2,-1,0,0,0][rank];ranks.append(rank)
        D={(y,x) for y in range(11) for x in range(11) if min(y,x)<9}|{(9,9)}
        rank=piece(D,[(y,10) for y in (0,3,6)]+[(10,x) for x in (0,3,6)],{(9,9)})
        cm=sum(r[y][x]=='#' for y,x in D if max(y,x)<10 and (y,x)!=(9,9))
        assert cm<=[36,36,37,38,38,39][rank];corner_r.append(rank)
        r=list(map(''.join,zip(*r[::-1])))
    b,_,ei,_,tree=joint(r,9)
    old9=marks(r)-marks([s[9:-9] for s in r[9:-9]])
    assert old9<=dense_cap(n)
    assert sum(ranks+corner_r)<=23
    cap=dense_cap(n)+(min(0,(15-bad)//9) if spaced else 0);assert old9<=cap
    result=cap+upper(n-18)-(ei-b)
    print('dense pitch ends: 9-layer count/cap',old9,dense_cap(n),
          'corner/side ranks',corner_r,ranks,'bad',bad,'priced cap',cap,'core-side gain',ei-b,
          'physical retained tree',tree,'upper',result)
    return result

if __name__=='__main__':
    from .end_band_obstruction import wrapped
    from .comb_cap_transfer import construct
    from .crop_end_coupling import locked_fringe
    for name,r in [('concentric',wrapped(103)),('comb',construct(103,4)),('locked',locked_fringe(103)),
                   ('complementary',punctures(103)),('double returns',punctures(103,True))]:
        r=verify(r,True)
        for d in ((9,) if 'returns' in name or name=='complementary' else (3,8,9)):
            print(name,verify(r)[0],d,estimate(r,d),flush=True)
        if name in ('complementary','double returns'):
            assert dense_transfer(r)<=comb(103)
