"""Two partition-free interior estimates using the actual collar on all four sides."""
from .sparse_component_exchange import Forest
from .wired_crop_exchange import ring
from .boundary_tooth_debit import upper as tooth_upper
from .dense_joint_collar import marks

def projected(rows,d):
    n=len(rows);s=n-2*d;F=Forest(n);dep=lambda i,j:min(i,j,n-1-i,n-1-j)
    for y,row in enumerate(rows):
        for x,v in enumerate(row):
            if dep(y,x)>d:continue
            for i,j in ((y+1,x),(y,x+1)):
                if max(i,j)<n and dep(i,j)<=d and '#' in (v,rows[i][j]):assert F.join((y,x),(i,j))
    R=[(y+d,x+d) for y,x in ring(s)];w=[rows[y][x] for y,x in R]
    h=w.count('.');g=sum(a==b=='.' for a,b in zip(w,w[1:]+w[:1]));e=len({F.root(v) for v in R})
    K=sum(rows[y][x]=='#' for y in (d,n-1-d) for x in (d,n-1-d))
    c=[row[d:n-d] for row in rows[d:n-d]];I=marks(c);T=marks(rows)-I
    numerator=4*s*s+14*s-18-4*h-4*g+3*K+6*e
    # Equality needs a literal rail core. Test its two orientations
    # against the actual rim, then glue its normal through paths.
    def can_equal(swap):
        coord=lambda y,x:(x,y) if swap else (y,x)
        rr=ring(s)
        for y,x in rr:
            i,j=coord(y,x);optional=i in (0,s-1) and j not in (0,s-1) and j%3==0
            if not optional and (c[y][x]=='#')!=(j%3==0):return False
        # The two extreme paths are already in the shared rim.
        P=Forest(n);labels={F.root(v):v for v in R}
        for j in range(3,s-1,3):
            a,b=coord(0,j),coord(s-1,j)
            if not P.join(labels[F.root((a[0]+d,a[1]+d))],labels[F.root((b[0]+d,b[1]+d))]):return False
        return True
    radial=(numerator-int(not any(can_equal(swap) for swap in (False,True))))//12
    # Choose the spaced teeth separately on the four sides. Assign corners
    # to one axis at a time. Segment directions need not be aligned.
    def at(side,j):
        return ((d,j+d),(n-d-1,j+d),(j+d,d),(j+d,n-d-1))[side]
    D=len(R)-h+K;best=10**9;stats=None
    for axis in (0,1):
        teeth=[]
        for side in range(4):
            loc=lambda j:rows[at(side,j)[0]][at(side,j)[1]]
            sel=[];prev=-3
            for j in range(s):
                if j in (0,s-1) and side//2!=axis:continue
                if j-prev<3 or loc(j)!='#' or j>0 and loc(j-1)=='#' or j+1<s and loc(j+1)=='#':continue
                sel.append(j);prev=j
            teeth.append(set(sel))
        ranks=[];t=sum(map(len,teeth))
        for side in (0,2):
            P=Forest(n);rho=0
            # Forest uses coordinates; select representatives from the
            # actual exterior classes for its test joins.
            lab={F.root(v):v for v in R}
            for j in teeth[side]&teeth[side+1]:
                if j in (0,s-1):
                    # A solid lateral boundary rail is already present
                    # in the shared rim, not a new interior join.
                    line=([r[j] for r in c] if side==0 else c[j])
                    rho+=all(v=='#' for v in line)
                    continue
                rho+=P.join(lab[F.root(at(side,j))],lab[F.root(at(side+1,j))])
            ranks.append(rho)
        u=(s*s+D-t+max(ranks)-(g-e+1))//3
        if u<best:best=u;stats=t,ranks
    u=min(radial,best,tooth_upper(c))
    assert u>=I,(u,I,h,g,e,stats)
    return T+u,(T,h,g,e,stats,T+radial,T+best)

if __name__=='__main__':
    from .dense_joint_collar import verify,punctures
    from .comb_cap_transfer import construct
    from .crop_end_coupling import locked_fringe
    for n in (103,133):
        for name,r in [('comb',construct(n,4)),('locked',locked_fringe(n)),('double',punctures(n,True))]:
            r=verify(r,True);print(n,name,projected(r,9))
