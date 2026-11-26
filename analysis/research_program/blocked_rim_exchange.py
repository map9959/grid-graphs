"""Joint two-layer straightening on the smaller square, priced by physical contacts."""
from .sparse_component_exchange import Forest,graph
from .extend_forest_28 import verify
from .crop_end_coupling import locked_fringe
from .collar_vacancies import comb

def pos(n,side,d,x):
    for _ in range(side):d,x=x,n-1-d
    return d,x

def exchange(rows,windows,rails=1):
    """Replace depths 0..3*(rails-1)+1; arbitrary exterior, including both ends."""
    n=len(rows);M={(i,j) for i,row in enumerate(rows) for j,v in enumerate(row) if v=='#'}
    D=set();support=set();ports=[];rim=set();roots=[];leaves=[]
    for w,(side,l,r) in enumerate(windows):
        assert 2<=l<=r-3 and r<=n-3
        at=lambda d,x:pos(n,side,d,x)
        assert rails>=1 and 3*rails<=n
        pad={at(d,j) for d in range(3*rails) for j in range(l-1,r+2)}
        assert not pad&support;support|=pad
        D.update(at(d,j) for d in range(3*rails-1) for j in range(l,r+1))
        for d in range(0,3*rails,3):
            idx=len(roots);roots.append(at(d,l+1))
            for j in range(l,r+1):
                v=at(d,j);rim.add(v)
                for dd in (d-1,d+1):
                    if dd>=0:leaves.append((idx,at(dd,j),v))
            for j,z,ext in ((l,l+1,l-1),(r,r-1,r+1)):
                v=at(d,j);p=at(d,ext)
                cut=(v,at(d,z)) if p in M else (v,)
                ports.append((len(cut),idx,p,cut))
    F=Forest(n);exterior=M-D
    attached=set()
    for y,x in exterior:
        for p in ((y,x-1),(y,x+1),(y-1,x),(y+1,x)):
            if not all(0<=j<n for j in p) or p in rim:continue
            if p in exterior and p<(y,x):continue
            assert F.join((y,x),p)
            if p in D:attached.add(p)
    for idx,p,v in leaves:
        if p in attached:ports.append((1,idx,p,(v,)))
    remove=set();debit=[0,0]
    for cost,w,p,cut in sorted(ports,reverse=True):
        if not F.join(roots[w],p):
            debit[cost-1]+=1;remove.update(cut)
    new=exterior|(rim-remove)
    out=[''.join('#' if (y,x) in new else '.' for x in range(n)) for y in range(n)]
    holes=len(rim-M);blockers=len((D-rim)&M)
    G=holes-blockers-debit[0]-2*debit[1]
    assert len(new)-len(M)>=G
    return out,(holes,blockers,*debit,G,len(new)-len(M))

def lock_windows(rows,h):
    n=len(rows);m=n-2*h
    c=[s[h:-h] for s in rows[h:-h]]
    W=[]
    for side in range(4):
        xp=[x for x in range(3,m-3) if c[pos(m,side,1,x)[0]][pos(m,side,1,x)[1]]=='#']
        W.append((side,min(xp)-1,max(xp)+1))
    return c,W

def inward_returns(rows,sites):
    """Close isolated holes at depth 3 after releasing the depth-1 blockers."""
    n=len(rows);F=graph(rows,set());out=list(map(list,rows));backed=joins=0
    for side,x in sites:
        at=lambda d,j:pos(n,side,d,j)
        def bit(d,j):
            y,z=at(d,j);return out[y][z]=='#'
        assert not bit(3,x) and bit(3,x-1) and bit(3,x+1)
        assert not any(bit(d,x+j) for d in (2,4) for j in (-1,0,1))
        assert not bit(1,x)
        backed+=bit(5,x)
        # The outward neighbour is isolated; the inward is isolated or
        # attached to its unique backing donor. Skip a dependent return.
        if not F.join(at(3,x),at(4,x)):
            assert bit(5,x)
            continue
        joins+=bit(5,x)
        assert F.join(at(3,x),at(2,x))
        y,z=at(3,x);out[y][z]='#'
    return [''.join(s) for s in out],(len(sites),backed,joins,len(sites)-backed+joins)

def checks():
    for n in (103,):
        orig=locked_fringe(n);start=verify(orig)
        for h in (3,6):
            c,w=lock_windows(orig,h);v=verify(c);new,data=exchange(c,w);tree=verify(new)
            loss=start[0]-v[0];m=n-2*h;k=m//3;upper=3*k*k+5*k+(k-5)//3
            result=loss+upper-data[-2]
            print('crop',m,'holes,blockers,rejected backs/ends,bound,actual',data,
                  'old/new physical trees',v,tree,'crop upper',upper-data[-2],
                  'transferred upper',result)
            assert result<=comb(n) and tree[0]-v[0]==data[-1]
            if h==6:
                sites=[(s,x) for s,l,r in w for x in range(l+1,r,3)]
                deep,ret=inward_returns(new,sites);v2=verify(deep)
                assert v2[0]-v[0]==64 and ret==(32,0,0,32)
                print('inward holes/backed/rank/gain',ret,'physical tree',v2,
                      'smaller upper',upper-64,'transferred upper',loss+upper-64)
    n=19;l,r=3,14
    M={(y,x) for x in range(l+1,r,3) for y in (0,1,2)}|{(4,x) for x in range(n)}
    board=[''.join('#' if (y,x) in M else '.' for x in range(n)) for y in range(n)]
    out,d=exchange(board,[(0,l,r)]);assert d==(8,4,3,0,1,1)
    print('four backed posts returning to one tree:',d,'repair',verify(out))
    n=193;s=25;r=locked_fringe(n,s);v=verify(r)
    c,W=lock_windows(r,6);m=n-12;k=m//3
    out,a=exchange(c,W);holes=[(i,x) for i,l,t in W for x in range(l+1,t,3)]
    deep,ret=inward_returns(out,holes);v2=verify(deep)
    removed=v[0]-sum(row.count('#') for row in c);U=3*k*k+5*k+(k-5)//3
    assert removed==8*n-46+4*s and a[-2]==ret[-1]==4*(s+1)
    print('variable train length',s,'removed',removed,'two gains',a[-2],ret[-1],
          'comb minus returned upper',comb(n)-(U+removed-a[-2]-ret[-1]),'tree',v2)
if __name__=='__main__':checks()
