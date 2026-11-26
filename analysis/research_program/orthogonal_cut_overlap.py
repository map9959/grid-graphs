"""Combine independently repaired row and column cuts; price only their common rank."""
from collections import defaultdict
from .skeleton_cross_rank import DSU
from .extend_forest_28 import verify
from .cross_minor_refill import refill


def edges(rows,y=None,x=None):
    """Edges on the retained sites, labelled in source coordinates."""
    n=len(rows);ys=[i for i in range(n) if i!=y];xs=[j for j in range(n) if j!=x]
    for k,i in enumerate(ys):
        for l,j in enumerate(xs):
            for u,v in ([(ys[k+1],j)] if k+1<len(ys) else [])+(
                        [(i,xs[l+1])] if l+1<len(xs) else []):
                m,p=rows[i][j],rows[u][v]
                if m==p=='.':continue
                axis=0
                if u-i==2 and rows[i+1][j]=='.' and m!=p:axis=1
                if v-j==2 and rows[i][j+1]=='.' and m!=p:axis=2
                yield axis,i*n+j,u*n+v,(i,j) if m=='#' else (u,v)


def line(rows,y=None,x=None):
    assert (x is None)!=(y is None)
    ds=DSU(len(rows)**2);pending=[];paid=set()
    for tag,u,v,owner in edges(rows,y,x):
        if tag:pending.append((u,v,owner))
        else:assert ds.join(u,v)
    for u,v,owner in pending:
        if not ds.join(u,v):paid.add(owner)
    return paid


def portal_rank(b,y,x):
    n=len(b);base=DSU(n*n);seam=[[],[]]
    for _,u,v,_ in edges(b,y,x):
        if v-u==2*n:seam[0].append((u,v))
        elif u//n==v//n and v-u==2:seam[1].append((u,v))
        else:assert base.join(u,v)
    endpoints=[{base.root(z) for e in pairs for z in e} for pairs in seam]
    shared=endpoints[0]&endpoints[1]
    def count(ds):return len({ds.root(z) for z in shared})
    subtotal=0
    both=DSU(n*n);both.p=base.p[:]
    for pairs in seam:
        ds=DSU(n*n);ds.p=base.p[:]
        for u,v in pairs:assert ds.join(u,v);both.join(u,v)
        subtotal+=count(ds)
    t=[0]*4
    for z in shared:
        i,j=divmod(z,n);t[2*int(i>y)+int(j>x)]+=1
    q=len(shared)-subtotal+count(both)
    assert q<=sum(max(z-1,0) for z in t)+int(all(t))
    return q,t


def joint(rows,y,x,row_paid=None,col_paid=None):
    n=len(rows)
    if row_paid is None:row_paid=line(rows,y=y)
    if col_paid is None:col_paid=line(rows,x=x)
    b=[list(r) for r in rows]
    for i,j in row_paid|col_paid:b[i][j]='.'
    ds=DSU(n*n);parts=[[],[]]
    for tag,u,v,owner in edges(b,y,x):
        if tag:parts[tag-1].append((u,v,owner))
        else:assert ds.join(u,v)
    saved=ds.p[:];choices=[]
    for first in (0,1):
        ds.p=saved[:]
        for u,v,_ in parts[first]:assert ds.join(u,v)
        choices.append({owner for u,v,owner in parts[1-first] if not ds.join(u,v)})
    q=len(choices[0]);assert len(choices[1])==q
    assert q==portal_rank(b,y,x)[0]
    def preloss(paid,y=None,x=None):
        return paid|{(i,j) for i in range(n) for j in range(n) if (i==y or j==x) and rows[i][j]=='#'}
    losses=[preloss(row_paid,y=y),preloss(col_paid,x=x)]
    raw=(len(losses[0]),len(losses[1]),len(losses[0]&losses[1]),q)
    paid=sum(raw[:2])-raw[2]+q
    opts=[]
    for choice in choices:
        a=[''.join('.' if (i,j) in choice else v for j,v in enumerate(r) if j!=x)
           for i,r in enumerate(b) if i!=y]
        assert sum(r.count('#') for r in rows)-sum(r.count('#') for r in a)==paid
        out,g=refill(a);opts.append((sum(g),out))
    gain,out=max(opts)
    return out,raw,gain


def isolate_price(rows,y):
    """Uniform-in-the-other-cut charge: unsupported bonds with a nonisolated blank head."""
    n=len(rows);p=rows[y].count('#')
    if y in (0,n-1):return p
    for x,m in enumerate(rows[y]):
        if m=='#' or rows[y-1][x]==rows[y+1][x]:continue
        i=y+(1 if rows[y+1][x]=='.' else -1)
        p+=any(rows[a][b]=='#' for a,b in ((i-1,x),(i+1,x),(i,x-1),(i,x+1))
               if 0<=a<n and 0<=b<n)
    return p


def isolate_cut(rows,y,x):
    n=len(rows);new=[list(r[:x]+r[x+1:]) for i,r in enumerate(rows) if i!=y]
    risky=set();free=defaultdict(list)
    for tag,u,v,mark in edges(rows,y,x):
        if not tag:continue
        i,j=divmod(v if divmod(u,n)==mark else u,n)
        if any(rows[a][b]=='#' for a,b in ((i-1,j),(i+1,j),(i,j-1),(i,j+1))
               if 0<=a<n and 0<=b<n):risky.add(mark)
        else:free[i,j].append(mark)
    # A doubly hit isolate is a central corner. Two such corners have
    # exactly the same pair of opposite marked owners.
    twice={tuple(sorted(ps)) for ps in free.values() if len(ps)>1}
    if twice:
        assert len(twice)==1 and rows[y][x]=='.'
        risky.add(next(iter(twice))[0])
    for i,j in risky:new[i-(i>y)][j-(j>x)]='.'
    out=[''.join(r) for r in new]
    upper=isolate_price(rows,y)+isolate_price(list(zip(*rows)),x)+1-2*(rows[y][x]=='#')
    assert sum(r.count('#') for r in rows)-sum(r.count('#') for r in out)<=upper
    return out,upper


def ring_example(k):
    """Every ring needs both cuts to close. Two independent seam repairs alone miss this."""
    n=6*k+7;mid=n//2
    from .wired_crop_exchange import ring
    marks=set()
    for h in range(k):
        d=3*h;s=n-2*d
        holes={(0,1),(1,s-1),(s-1,s-2),(s-2,0),
               (mid-d,0),(mid-d+1,0),(0,mid-d),(0,mid-d+1)}
        marks.update((d+i,d+j) for i,j in ring(s) if (i,j) not in holes)
    return [''.join('#' if (i,j) in marks else '.' for j in range(n)) for i in range(n)]


if __name__=='__main__':
    from .cross_minor_refill import shell_control
    from .comb_cap_transfer import construct
    for k in (1,4,16):
        a=ring_example(k);n=len(a);mid=n//2
        assert not line(a,y=mid) and not line(a,x=mid)
        out,raw,g=joint(a,mid,mid);assert raw[3]==k
        print('ring side',n,'source',verify(a)[0],'single-cut repairs 0,0; common rank',k,'tree',verify(out))
    src=refill([('#' if i%3==1 else '.')*5+'.'+r[6:] for i,r in enumerate(construct(103,4))])[0]
    for rows in (src,refill(['.'+r[:-1] for r in shell_control(103)])[0]):
        from .skeleton_cross_rank import physical
        for y,x in ((2,2),(37,49)):
            out,raw,g=joint(rows,y,x);tree=verify(out)
            loss=raw[0]+raw[1]-raw[2]+raw[3]-g
            assert loss==verify(rows)[0]-tree[0]
            print('103 (F,j,A,X)',physical(rows),'cut',(y,x),raw,'refill',g,'loss',loss,'tree',tree)
