"""Optimal pitch refill of two three-row bands against the same physical exterior."""
from .sparse_component_exchange import Forest,repair
from .comb_cap_transfer import construct
from .extend_forest_28 import verify

def refill(rows,ys,l,r,centers,allow_delete=True,bad_only=False,ledger=None):
    n=len(rows);centers=tuple(centers)
    assert all(1<=y<n-1 for y in ys) and all(v-u>=5 for u,v in zip(ys,ys[1:]))
    assert centers and all(v-u==3 for u,v in zip(centers,centers[1:]))
    assert l<=centers[0]<=l+1 and r-1<=centers[-1]<=r
    tiles=[(y,c) for y in ys for c in centers if not bad_only or
           any((rows[y][x]=='#')!=(x==c) for x in range(max(l,c-1),min(r,c+1)+1))]
    D={(i,x) for y,c in tiles for i in range(y-1,y+2) for x in range(max(l,c-1),min(r,c+1)+1)}
    # At a good pitch triple its two outside columns are empty on the
    # normal rows by diagonal exclusion. Check every lateral contact.
    for i,x in D:
        for j in (x-1,x+1):
            if 0<=j<n and (i,j) not in D:assert x not in centers and rows[i][j]=='.'
    out=list(map(list,rows));old=sum(out[i][x]=='#' for i,x in D)
    for i,x in D:out[i][x]='.'
    def exterior():
        F=Forest(n)
        for i in range(n):
            for x in range(n):
                if (i,x) in D:continue
                for u,v in ((i+1,x),(i,x+1)):
                    if u>=n or v>=n or (u,v) in D:continue
                    if out[i][x]=='#' or out[u][v]=='#':assert F.join((i,x),(u,v))
        return F
    ports=[((y,x),(y+s,x),(y+2*s,x)) for y,x in tiles for s in (-1,1)]
    F=exterior();removed=[]
    for tooth,_,(i,x) in ports:
        if 0<=i<n and out[i][x]=='#' and not F.join(tooth,(i,x)):
            removed.append((i,x))
    if removed and not allow_delete:return None
    for i,x in removed:out[i][x]='.'
    F=exterior()
    for tooth,_,(i,x) in ports:
        if 0<=i<n and out[i][x]=='#':assert F.join(tooth,(i,x))
    if ledger is not None:
        ledger.update(tiles=D,clipped=set(removed),
                      compulsory=[(t,v) for t,_,v in ports if 0<=v[0]<n and out[v[0]][v[1]]=='#'],
                      optional=[])
    free=rank=blocked=0
    for tooth,(y,j),(i,x) in ports:
        out[tooth[0]][tooth[1]]='#'
        if 0<=i<n and any(out[i][z]=='#' for z in (x-1,x+1) if 0<=z<n):
            blocked+=1;continue
        if not 0<=i<n or out[i][x]=='#':free+=1
        else:
            if ledger is not None:ledger['optional'].append((tooth,(i,x)))
            if F.join(tooth,(i,x)):rank+=1
            else:continue
        out[y][j]='#'
    out=[''.join(r) for r in out];base=len(ports)//2
    gain=base+free+rank-len(removed)-old
    assert sum(row.count('#') for row in out)-sum(row.count('#') for row in rows)==gain
    return out,(old,base,free,rank,blocked,len(removed),gain)

def combine(rows,a,b,bad_only=False):
    n=len(rows);sr,mid=repair(rows,a,b,with_rows=True)
    out,er=refill(mid,[a,b],5,n-6,range(6,n-4,3),bad_only=bad_only)
    assert all(out[y][3]==out[y][-4]=='#' for y in range(a,b+1))
    assert all((out[y][x]=='#')==(x%3==0) for y in (a,b) for x in range(3,n-3))
    tree=verify(out);k=n//3;comb=3*k*k+5*k+(3*k-13)//10
    assert tree[0]<=comb
    upper=comb-sr[5]-er[-1]
    assert sum(row.count('#') for row in rows)<=upper
    return sr,er,tree,upper

def test(n):
    rows=construct(n,4);a,b=4,n-10;mid=n//2
    # Replace isolated stretches of vertical rail by displaced marks
    # at both ends. A small vertical off-phase run dirties ALL northern
    # cuts at depths 1..9. It is separated from the other forced stars.
    marks={(y,x) for y,row in enumerate(rows) for x,v in enumerate(row) if v=='#'}
    def insert(group):
        nonlocal marks
        marks-={(y+i,x+j) for y,x in group for i in range(-2,3) for j in range(-2+abs(i),3-abs(i))}
        marks|=group
    insert({(i,10) for i in range(1,10)})
    insert({(b,16)})
    insert({(mid,1),(mid,5)})
    rows=[''.join('#' if (i,x) in marks else '.' for x in range(n)) for i in range(n)]
    print(n,'initial tree',verify(rows))
    for sparse in (False,True):
        sr,er,tree,upper=combine(rows,a,b,sparse)
        print('only defective triples',sparse,'side gain',sr[5],'end inventory (old,centers,free,rank,blocked,repairs,gain)',er,
              'final tree',tree,'returned upper',upper)
if __name__=='__main__':test(103)
