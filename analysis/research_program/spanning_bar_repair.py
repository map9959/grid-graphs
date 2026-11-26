"""Complete a spanning bar against its two actual, independent half-squares."""
from .sparse_component_exchange import graph
from .extend_forest_28 import verify

def repair(rows,y):
    n=len(rows);out=list(map(list,rows));holes={j for j,v in enumerate(rows[y]) if v=='.'}
    # Components of the OLD row containing a mark, including single blanks
    # between consecutive marks in the same component.
    js=[j for j in range(n) if j not in holes]
    splits=sum(b-a>=3 for a,b in zip(js,js[1:]))
    A=Q=0
    for sign in (-1,1):
        t=y+sign;u=y+2*sign
        if not 0<=t<n:continue
        a=sum(v=='#' for v in out[t]);out[t]=['.']*n;A+=a
        q=0
        if 0<=u<n:
            for j in holes:
                if out[u][j]=='#':q+=1;out[u][j]='.'
        Q+=q
        assert a+q<=len(holes)+int(n%2 and len(holes)>=n//2)
    out[y]=['.']*n
    F=graph(out,set());seen=set();extra=0
    for u in (y-2,y+2):
        if not 0<=u<n:continue
        for j in js:
            if out[u][j]!='#':continue
            z=F.root((u,j))
            if z in seen:out[u][j]='.';extra+=1
            seen.add(z)
    assert extra<=splits
    out[y]=['#']*n;out=[''.join(r) for r in out]
    tree=verify(out)
    assert tree[0]==sum(r.count('#') for r in rows)+len(holes)-A-Q-extra
    return out,(len(holes),splits,A,Q,extra,tree)

if __name__=='__main__':
    from .comb_cap_transfer import construct
    n=103;rows=construct(n,4)
    for y in (1,2,3,49,100,101):
        for r in (rows,[''.join(c) for c in zip(*rows)]):
            print('repair',y,repair(r,y)[1])
