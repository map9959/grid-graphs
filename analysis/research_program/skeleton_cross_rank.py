"""Physical off-skeleton join rank, and cut/refill with a fixed repaired skeleton."""
from itertools import product
from .pitch_skeleton_ledger import ledger
from .cross_minor_price import repair,verify
from .cross_minor_refill import refill


class DSU:
    def __init__(self,n):self.p=list(range(n))
    def root(self,u):
        p=self.p
        while u!=p[u]:p[u]=p[p[u]];u=p[u]
        return u
    def join(self,u,v):
        a,b=self.root(u),self.root(v);self.p[a]=b
        return a!=b


def graphs(rows):
    n=len(rows)
    for u in range(n*n):
        i,j=divmod(u,n)
        for v in ([u+1] if j+1<n else [])+([u+n] if i+1<n else []):
            a,b=divmod(v,n)
            if rows[i][j]=='#' or rows[a][b]=='#':yield u,v


def split(rows):
    return [''.join('.' if i%3 and j%3 else c for j,c in enumerate(r)) for i,r in enumerate(rows)]


def physical(rows):
    n=len(rows);m=(n+2)//3
    M,F,r,c,C,sl=ledger(rows)
    sk=set(graphs(split(rows)));ds=DSU(n*n)
    for u,v in sk:assert ds.join(u,v)
    J=[i*n+j for i,j in product(range(0,n,3),repeat=2)]
    assert len({ds.root(u) for u in J})==C
    for u,v in graphs(rows):
        if (u,v) not in sk:assert ds.join(u,v)
    A=len({ds.root(u) for u in J});rank=C-A
    pitch='#..'*(m-1)+'#'
    if pitch not in rows and tuple(pitch) not in zip(*rows):
        extra=sl[0]+(sl[1]-(2*m-r-c))+sl[2]
        assert sl[1]>=2*m-r-c and extra>=0
        assert M==n*m+(F-rank)-A-extra
        empty=sum(not any(rows[a][b]=='#' for a,b in
                      ((i-1,h),(i+1,h),(i,h-1),(i,h+1)) if 0<=a<n and 0<=b<n)
                  for i,h in product(range(0,n,3),repeat=2))
        if empty<m*m:assert M+empty<=n*m+F-rank-1
    else:extra=None
    return F,rank,A,extra


def uniform_lines(rows):
    """Extra restrictions inside three neighboring all-vertical junction rows."""
    o={};_,_,r,c,_,s=ledger(rows,field=o)
    F,j,A,extra=physical(rows);assert extra is not None
    n=len(rows);m=(n+2)//3
    if c<r:
        rows=[''.join(col) for col in zip(*rows)]
        o={(i,h):('V' if a=='H' else 'H') for (h,i),a in o.items()}
    pure=[all(o[i,h]=='V' for h in range(m)) for i in range(m)]
    kind=[0]*4
    for i in range(m):
        if not all(pure[max(0,i-1):min(m,i+2)]):continue
        rail=rows[3*i][::3]
        sides=[rows[y][::3] for y in (3*i-1,3*i+1) if 0<=y<n]
        if any('.' not in mid for mid in sides):kind[0]+=1
        elif any(a=='#' and z=='.' for mid in sides for a,z in zip(rail,mid)):kind[1]+=1
        elif rail.count('.')>=2:kind[2]+=1
        else:
            assert rail.count('.')==1 and all(mid[rail.index('.')]=='.' for mid in sides)
            kind[3]+=1
    assert kind[0]<=j and kind[1]<=2*s[0] and kind[2]<=s[1]-(2*m-r-c)
    isolated=sum(rows[i][h]=='.' and all(rows[u][v]=='.' for u,v in
                 ((i-1,h),(i+1,h),(i,h-1),(i,h+1)) if 0<=u<n and 0<=v<n)
                 for i,h in product(range(0,n,3),repeat=2))
    assert kind[3]<=isolated<=A
    assert sum(kind)>=m-3*min(r,c)
    return tuple(kind)


def cross(rows,y,x):
    n=len(rows);w=n-1;part,qs,ps=repair(split(rows),y,x)
    base=set(graphs(part));d=DSU(w*w)
    for u,v in base:assert d.join(u,v)
    target=[list(r) for r in part];sites=set()
    for i,j in product(range(w),repeat=2):
        a=i+(i>=y);b=j+(j>=x)
        if a%3 and b%3 and rows[a][b]=='#':sites.add(i*w+j);target[i][j]='#'
    # Extend a spanning forest keeping double-owned edges first. Dropping
    # all owners of the rejected edges leaves the old skeleton intact.
    pending=[(u,v) for u,v in graphs(target) if (u,v) not in base]
    rejected=set();qd=q=0
    for u,v in sorted(pending,key=lambda uv:not all(z in sites for z in uv)):
        if not d.join(u,v):
            owners=sites.intersection((u,v));assert owners
            rejected.update(owners);q+=1;qd+=len(owners)==2
    for u in rejected:target[u//w][u%w]='.'
    erased=rows[y].count('#')+sum(row[x]=='#' for row in rows)-int(rows[y][x]=='#')
    out=[''.join(r) for r in target]
    assert sum(s.count('#') for s in rows)-sum(s.count('#') for s in out)==erased+ps+len(rejected)
    assert len(rejected)<=q+qd
    out,gains=refill(out)
    loss=erased+ps+len(rejected)-sum(gains)
    return out,(erased,ps,q,qd,len(rejected),sum(gains),loss)


def lift(rows,y,x):
    """Carry over distant off-skeleton stars after the skeleton seam is repaired."""
    from .cross_rail_slab import repair as break_turns
    n=len(rows);w=n-1;sk=split(rows);old=DSU(n*n)
    oe=set(graphs(sk))
    for u,v in oe:assert old.join(u,v)
    junction={old.root(i*n+j) for i,j in product(range(0,n,3),repeat=2)}
    kept=[list(r) for r in sk];near=0
    base,_,_=repair(sk,y,x);out=[list(r) for r in base]
    def project(z):
        i,j=divmod(z,n);assert i!=y and j!=x
        return (i-(i>y))*w+j-(j>x)
    for i,j in product(range(n),repeat=2):
        if i%3 and j%3 and rows[i][j]=='#':
            if min(abs(i-y),abs(j-x))<3:near+=1;continue
            kept[i][j]='#';u,v=divmod(project(i*n+j),w);out[u][v]='#'
    extra=set(graphs(kept))-oe
    ports={z for e in extra for z in e if old.root(z) in junction}
    nc0=len({old.root(z) for z in ports})
    for u,v in extra:assert old.join(u,v)
    j0=nc0-len({old.root(z) for z in ports})
    new=DSU(w*w);be=set(graphs(base))
    for u,v in be:assert new.join(u,v)
    nx={(project(u),project(v)) for u,v in extra}
    assert nx==set(graphs(out))-be
    proj=list(map(project,ports));nc1=len({new.root(z) for z in proj})
    cycles=sum(not new.join(u,v) for u,v in nx)
    j1=nc1-len({new.root(z) for z in proj})
    assert cycles==j0-j1
    fixed,dropped=break_turns(out);assert dropped<=cycles
    final,g=refill(fixed)
    L=sum(r.count('#') for r in sk)-sum(r.count('#') for r in base)
    loss=sum(r.count('#') for r in rows)-sum(r.count('#') for r in final)
    assert loss==L+near+dropped-sum(g)
    return final,(L,near,j0,j1,dropped,sum(g),loss)


if __name__=='__main__':
    from .comb_cap_transfer import construct
    from .cross_minor_refill import shell_control
    comb=construct(103,4)
    cases=[(name,['.'+r[:-1] for r in b]) for name,b in
           [('shift-comb',comb),('shift-shell',shell_control(103))]]
    cases.append(('mixed',[(5*('#' if i%3==1 else '.')+'.'+r[6:]) for i,r in enumerate(comb)]))
    for name,b in cases:
        rows=refill(b)[0]
        F,j,A,extra=physical(rows);assert F>=43 and extra is not None
        print(name,'deep uniform lines:',uniform_lines(rows))
        src=verify(rows);assert src[0]==src[-1] and src[0]==3605+F-j-A-extra
        # Keep a finite set of genuinely interior crosses as well as boundary cuts.
        for cuts in [[(y,x) for y in (1,2,37,49) for x in (13,17,37,49)],[(y,0) for y in (1,2,37,49)]]:
            out,t=min((cross(rows,y,x) for y,x in cuts),key=lambda z:z[1][-1])
            dst=verify(out);assert dst[0]==src[0]-t[-1]
            print(name,'source',src[0],'(F,joins,A,excess)',(F,j,A,extra),
                  'cut charges (erased,skeleton,cycles,double,paid,refill,loss)',t,'tree',dst)
        for y,x in ((37,49),(2,2)):
            out,t=lift(rows,y,x);dst=verify(out);assert dst[0]==src[0]-t[-1]
            print('lift',name,(y,x),'skeleton loss, near, old/new joins, repaired, refill, loss:',t,'tree',dst)
