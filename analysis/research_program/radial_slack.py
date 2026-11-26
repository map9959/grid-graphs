"""Radial induction budget, with the physical gluing slack distinguished."""
from .dense_joint_collar import marks,verify,comb
from .sparse_component_exchange import Forest,graph
from .wired_crop_exchange import ring

def interface(rows):
    n=len(rows);R=ring(n);w=[rows[i][j] for i,j in R]
    F=graph(rows,set());c=len({F.root(p) for p in R})
    return w.count('.'),sum(a==b=='.' for a,b in zip(w,w[1:]+w[:1])),sum(rows[y][x]=='#' for y in (0,n-1) for x in (0,n-1)),c

def slack(rows):
    s=len(rows);I=marks(rows);h,g,k,c=interface(rows)
    return 4*s*s+14*s-12-(12*I+4*h-2*g-3*k+6*c)

def bands(rows):
    r=rows;total=slack(r);local=[];lost=[]
    while len(r)>=10:
        n=len(r);s=n-6;t=[w[3:-3] for w in r[3:-3]];h,g,k,c=interface(r);a,b,d,e=interface(t)
        F=Forest(n);dep=lambda y,x:min(y,x,n-1-y,n-1-x)
        for y in range(n):
            for x in range(n):
                if dep(y,x)>3:continue
                for i,j in ((y+1,x),(y,x+1)):
                    if max(i,j)<n and dep(i,j)<=3 and '#' in (r[y][x],r[i][j]):assert F.join((y,x),(i,j))
        u=len({F.root(v) for v in [*ring(n),*((y+3,x+3) for y,x in ring(s))]})
        S=48*n-60-(12*(marks(r)-marks(t))+4*(h-a)-2*g-4*b-3*(k-d)+6*u)
        G=u+e-b-c
        assert S>=0 and G>=0
        local.append(S);lost.append(6*G);r=t
    assert slack(r)>=0 and sum(local)+sum(lost)+slack(r)==total
    return total,local,lost,slack(r)

if __name__=='__main__':
    from .comb_cap_transfer import construct
    from .end_band_obstruction import wrapped
    for n in (103,133):
        for name,f in [('comb',lambda n:construct(n,4)),('nested',wrapped)]:
            r=verify(f(n),True);print(n,name,bands(r))
