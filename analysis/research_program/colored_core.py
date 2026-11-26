"""Price an arbitrary rectangular interior by the run neighborhoods on its rim."""
from itertools import product
from .sparse_component_exchange import Forest

def weights():
    # Length-three extensions of any run have total color zero.
    for a in ((2,-1,-1),(1,1,-2)):
        for p in range(3):
            for axis in range(2):
                yield tuple(a[(v[axis]-p)%3] for v in product(range(3),repeat=2))
    for x,y in product(range(3),repeat=2):
        yield tuple(2*((i-x)%3==(j-y)%3)-((i-x)%3!=(j-y)%3)
                    for i,j in product(range(3),repeat=2))

def projection(rows,box,colors=None):
    n=len(rows);y0,y1,x0,x1=box;H=y1-y0+1;W=x1-x0+1;assert min(H,W)>=4
    R=[(y0,j) for j in range(x0,x1)]+[(i,x1) for i in range(y0,y1)]+[
        (y1,j) for j in range(x1,x0,-1)]+[(i,x0) for i in range(y1,y0,-1)]
    rim=set(R);M={v for v in R if rows[v[0]][v[1]]=='#'}
    F=Forest(n);edge=Forest(n);run=Forest(n);out=0;I=0
    for i,row in enumerate(rows):
        for j,v in enumerate(row):
            if y0<=i<=y1 and x0<=j<=x1:I+=v=='#'
            else:out+=v=='#'
            if y0<i<y1 and x0<j<x1:continue
            for a,b in ((i+1,j),(i,j+1)):
                if a<n and b<n and not(y0<a<y1 and x0<b<x1) and '#' in (v,rows[a][b]):
                    assert F.join((i,j),(a,b))
    for a,b in zip(R,R[1:]+R[:1]):
        if a in M or b in M:edge.join(a,b)
        if a in M and b in M:run.join(a,b)
    jmin=len({edge.root(v) for v in M})-len({F.root(v) for v in M})+bool(M)
    groups={}
    for v in M:groups.setdefault(run.root(v),set()).add(v)
    groups=list(groups.values())
    G={v:i for i,S in enumerate(groups) for v in S}
    cand=[set() for _ in groups];bridge=set()
    for dy,dx in ((1,0),(0,1)):
        for S in groups:
            y,x=min(S)
            if any((j!=x if dy else i!=y) for i,j in S):continue
            # A straight run on the rim itself has known endpoints.
            if (dy and x in (x0,x1)) or (dx and y in (y0,y1)):
                cand[G[y,x]].add((y%3,x%3,dy,len(S)%3));continue
            # Otherwise it starts at a singleton and runs inward.
            assert len(S)==1
            far=(y1 if y==y0 else y0,x) if dy else (y,x1 if x==x0 else x0)
            sign=1 if far>(y,x) else -1;dim=H if dy else W
            for L in range(1,dim+1):
                if L==dim and (far not in M or len(groups[G[far]])!=1):continue
                if L==dim-1 and far in M:continue
                a,b=(y,x) if sign==1 else (y-dy*(L-1),x-dx*(L-1))
                t=(a%3,b%3,dy,L%3);cand[G[y,x]].add(t)
                if L==dim and sign==1:bridge.add((G[y,x],G[far],t))
    outside=[(y+dy,x+dx) for y,x in M for dy,dx in ((0,1),(0,-1),(1,0),(-1,0))
             if not(y0<=y+dy<=y1 and x0<=x+dx<=x1)]
    def forest(cost):
        P=Forest(n);gain=0;rep=[divmod(F.root(min(S)),n) for S in groups]
        for v,a,b in sorted(cost,reverse=True):
            if v>0 and P.join(rep[a],rep[b]):gain+=v
        return gain
    rmin=len(groups)-forest([(1,a,b) for a,b,t in bridge]);lb=rmin+jmin
    for vals in weights() if colors is None else colors:
        assert sum(vals)==0
        chi=lambda i,j:vals[3*(i%3)+j%3]
        w={}
        for y,x,dy,L in product(range(3),range(3),range(2),(1,2,3)):
            dx=1-dy
            w[y,x,dy,L%3]=chi(y-dy,x-dx)+chi(y+L*dy,x+L*dx)+sum(
                chi(y+i*dy+d*dx,x+i*dx+d*dy) for i in range(L) for d in (-1,0,1))
        lo=min(w.values());hi=max(vals)
        base=[min(w[t] for t in ts)-lo for ts in cand]
        bonus=sum(base)-forest([(base[a]+base[b]-w[t]+lo,a,b) for a,b,t in bridge])
        E=sum(chi(y,x) for y,x in outside)+sum(chi(y,x)*len(range(y,y1+1,3))*len(range(x,x1+1,3))
            for y,x in product(range(y0,y0+3),range(x0,x0+3)))
        div=max(hi-lo,-min(vals));lb=max(lb,jmin+-((E-bonus-hi*jmin)//div))
    ub=(H*W+len(outside)-lb)//3
    assert I<=ub,(box,I,ub)
    return out+ub,(jmin,rmin,lb,I,ub)

if __name__=='__main__':
    from .comb_cap_transfer import construct
    from .crop_end_coupling import locked_fringe
    from .dense_joint_collar import punctures
    n=103
    for r in (construct(n,4),locked_fringe(n),punctures(n,True)):
        print(min((projection(r,(y,n-1-y,x,n-1-x))[0],y,x) for y,x in product(range(2,13),repeat=2)))
