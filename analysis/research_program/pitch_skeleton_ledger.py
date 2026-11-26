"""Joint pitch-row and pitch-column accounting on the subdivided coarse grid."""
from itertools import product
from .extend_forest_28 import verify


def ledger(rows,empty='H',field=None):
    n=len(rows);k=n//3;m=k+1
    assert n==3*k+1 and k>=1
    inside=lambda y,x:0<=y<n and 0<=x<n
    def mark(y,x):return inside(y,x) and rows[y][x]=='#'
    nodes=list(product(range(m),repeat=2));o={};vac=set()
    for i,j in nodes:
        y,x=3*i,3*j
        h=mark(y,x-1) or mark(y,x+1);v=mark(y-1,x) or mark(y+1,x)
        assert not(h and v)
        o[i,j]='H' if h else 'V' if v else empty
        if not mark(y,x):vac.add((i,j))
    r=sum(any(o[i,j]=='H' for j in range(m)) for i in range(m))
    c=sum(any(o[i,j]=='V' for i in range(m)) for j in range(m))
    runs=sum(v=='H' and o.get((i,j-1))!='H' or v=='V' and o.get((i-1,j))!='V'
             for (i,j),v in o.items())
    ext=sum(int(j==0)+int(j==k) if v=='H' else int(i==0)+int(i==k) for (i,j),v in o.items())
    stubs=sum(mark(3*i+d,3*j+e) for i,j in nodes for d,e in [(0,1),(0,-1),(1,0),(-1,0)])
    missing=2*m*m-stubs-ext
    pred=actual=0;hits={p:0 for p in vac}
    for i,j in nodes:
        for d,e,axis in ((1,0,'V'),(0,1,'H')):
            nei=i+d,j+e
            if nei not in o:continue
            wants=[o[i,j]==axis,o[nei]==axis]
            mids=[mark(3*i+d,3*j+e),mark(3*i+2*d,3*j+2*e)]
            if not any(wants):continue
            pred+=1
            if any(mids) and (mids[0] or (i,j) not in vac) and (mids[1] or nei not in vac):
                actual+=1
            elif mids==wants:
                assert wants.count(False)==1
                p=((i,j),nei)[wants.index(False)]
                hits[p]+=1
    components=m*m-actual
    doubles=sum(v==2 for v in hits.values())
    assert pred==m*m+runs-ext and max(hits.values(),default=0)<=2
    slack=(missing+sum(hits.values())-(pred-actual),
           len(vac)+doubles-sum(hits.values()),runs-r-c-doubles)
    assert min(slack)>=0 and components>=1
    f=sum(mark(i,j) for i,j in product(range(n),repeat=2) if i%3 and j%3)
    M=sum(row.count('#') for row in rows)
    assert M==3*m*m+f-r-c-components-sum(slack)
    assert r+c+components>=m+2
    if field is not None:field.update(o)
    return M,f,r,c,components,slack


def mixed_gaps(rows):
    """F-sites in separated intervals. A deficit certifies a strict physical gain."""
    from .cross_rail_slab import normalize
    field={};M,F,r,c,_,_=ledger(rows,field=field)
    n=len(rows);m=(n+2)//3;pitch='#..'*(m-1)+'#'
    assert pitch not in rows and tuple(pitch) not in zip(*rows)
    if r<=c:gates=[3*i for i in range(m) if any(field[i,j]=='H' for j in range(m))]
    else:
        rows=[''.join(col) for col in zip(*rows)]
        gates=[3*j for j in range(m) if any(field[i,j]=='V' for i in range(m))]
    low=0;maxgain=0
    for a,b in zip([-1,*gates],[*gates,n]):
        block=rows[a+1:b];L=len(block)
        if not L:continue
        f=sum(s.count('#')-s[::3].count('#') for s in block)
        assert f==sum(s.count('#')-s[::3].count('#') for i,s in enumerate(block,a+1) if i%3)
        if a==-1 and b==n:need=(n+1)//2
        elif a==-1 or b==n:need=L//2  # ceil((L-1)/2)
        else:need=max(0,(L-2)//3)  # ceil((L-4)/3)
        low+=need
        if f>=need:continue
        if a==-1 and b==n:tree=verify([pitch]*n)
        elif a==-1 or b==n:
            rr=rows if a==-1 else rows[::-1]
            gate=''.join(x if y=='#' else '.' for x,y in zip(rr[L-1],pitch))
            tree=verify([pitch]*(L-1)+[gate]+rr[L:])
        else:_,tree=normalize(rows,a+1,b-1)
        assert tree[0]>M
        maxgain=max(maxgain,tree[0]-M)
    assert low>=m-min(r,c)
    assert maxgain or F>=low
    return low,maxgain


def anchored_pairs(rows):
    """Count two adjacent off-skeleton marks already attached to coarse junctions."""
    n=len(rows)
    def near(j):return j-1 if j%3==1 else j+1
    anchored={(i,j) for i,j in product(range(n),repeat=2) if i%3 and j%3 and
              rows[i][j]=='#' and '#' in (rows[near(i)][j],rows[i][near(j)])}
    return sum((i+d,j+e) in anchored for i,j in anchored for d,e in [(1,0),(0,1)])


if __name__=='__main__':
    from .comb_cap_transfer import construct
    from .cross_minor_refill import shell_control
    for n in (4,7,103):
        k=n//3;rows=['#'*n,'.'*n]+['#..'*k+'#']*(n-2)
        replay=verify(rows)
        print('skeleton',n,ledger(rows),'physical tree',replay)
        assert replay[0]==3*k*k+5*k and replay[-1]==replay[0]
    for rows in (construct(103,4),shell_control(103)):
        record=ledger(rows);p=anchored_pairs(rows);assert p<record[4]
        print('side 103 exterior marks and slack:',record,'anchored pairs',p)
    from .cross_minor_price import scattered
    for rows in (scattered(construct(103,4)),shell_control(103)):
        print('no pitch; mixed gap requirement and largest replayed gain',mixed_gaps(rows))
