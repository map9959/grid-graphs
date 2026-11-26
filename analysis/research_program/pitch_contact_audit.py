"""Independent physical checks of pitch-row credits, two-cap ranks and wire repair."""
from itertools import product
from .pitch_skeleton_ledger import ledger
from .skeleton_cross_rank import DSU,graphs
from .skeleton_floor_words import priced
from .four_square import masks4
from .reflected_pitch_rank import ledger as caprank
from .pitch_cap_partner import spectrum,upper
from .extend_forest_28 import verify
from .comb_cap_transfer import construct


def count(rows):
    n=len(rows);p='#..'*(n//3)+'#';tr=[''.join(c) for c in zip(*rows)]
    T=rows[::3].count(p)+tr[::3].count(p)
    for grid in (rows,tr):
        M,F,_,_,C,_=ledger(grid,empty='V');D=P=0
        for w in grid[::3]:
            ls=[tuple(int(0<=z<n and w[z]=='#') for z in (i-1,i,i+1)) for i in range(0,n,3)]
            s=('pre' if any(l or r for l,_,r in ls) else 'p0',None,0)
            for k,a in enumerate(ls):
                s,v=priced(s,a,k+1==len(ls),allow_zero=True);D+=v
            P+=s[0]=='p0'
        assert P==grid[::3].count(p) and D<=n*(n//3+1)+F-C-M+T
    return T


def small(n,h):
    out={};r=n//3+1
    for m in range(1<<(n*h)):
        free=[''.join('#' if m>>(n*i+x)&1 else '.' for x in range(n)) for i in range(h)]
        cycle,j=caprank(['#..'*(r-1)+'#',*free])
        if not cycle:out[j]=max(out.get(j,-999),m.bit_count()-h*r)
    assert out==spectrum(n,h)


def repair(rows,h):
    n=len(rows);out=['#'*n,'.'*n]+[rows[h]]*(h-1)+rows[h+1:]
    lost=0
    while True:
        d=DSU(n*n);adj=[[] for _ in range(n*n)]
        for u,v in graphs(out):
            if not d.join(u,v):break
            adj[u].append(v);adj[v].append(u)
        else:break
        parent={u:None};todo=[u]
        for x in todo:
            if x==v:break
            for y in adj[x]:
                if y not in parent:parent[y]=x;todo.append(y)
        cyc=[(u,v)];q=v
        while q!=u:cyc.append((q,parent[q]));q=parent[q]
        def mark(i):return out[i//n][i%n]=='#'
        site=next(a for u,v in cyc for a,b in ((u,v),(v,u)) if a//n>h and mark(a) and not mark(b))
        i,z=divmod(site,n);out[i]=out[i][:z]+'.'+out[i][z+1:];lost+=1
    return lost,verify(out)


if __name__=='__main__':
    for m in masks4():count([''.join('#' if m>>(4*i+j)&1 else '.' for j in range(4)) for i in range(4)])
    for h in (0,1,2):small(7,h)
    print('row-credit audits:',len(masks4()),'acyclic 4x4 masks; independent cap spectra agree at width 7')
    n=103;p='#..'*34+'#'
    for s in (30,32,34):
        rows=['#'*(3*s+1)+'.'*(102-3*s),'.'*n]+[p]*99+['.'*n,'.'*(3*s)+'#'*(103-3*s)]
        ju=caprank(rows[2::-1])[1];jd=caprank(rows[2:])[1]
        assert (ju,jd)==(s,34-s)
        before=verify(rows);lost,after=repair(rows,2)
        assert lost<=jd and after[0]>=before[0]
        print('cap ranks',ju,jd,'repair removals',lost,'physical scores',before[0],after[0])
    comb=construct(n,4);print('known comb',verify(comb),'aligned pitch lines',count(comb))
    costs=[]
    for i,w in enumerate(comb):
        if w!=p:continue
        cs=(comb[i::-1],comb[i:])
        js=[]
        for cap in cs:
            cyc,j=caprank(cap);assert not cyc;js.append(j)
            h=len(cap)-1;b=sum(r.count('#') for r in cap[1:])-35*h
            if h>=2:assert 3*b<=68+j-3
        assert sum(js)<=34;costs.append(sum(js))
    print('comb physical pitch splits',len(costs),'total join range',min(costs),max(costs))
    from .free_face_audit import check
    from .rank44_faces import test
    chart=test(weighted=True,free=True,price_pure=True,cuts=False)
    check(comb,chart,allow_pure=True)
    for h in (2,3,4):
        b=spectrum(n,h);u=upper(n,b)
        assert all(b[j]<=j-1 for j,v in u.items() if v>=3647)
