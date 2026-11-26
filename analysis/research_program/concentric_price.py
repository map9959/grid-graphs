"""Unrestricted multiscale comparison using only concentric boundary words."""
from .dense_joint_collar import comb,upper,marks,verify,punctures

def rim(rows):
    n=len(rows);hs=gs=0
    for _ in range(4):
        w=rows[0];hs+=w[:-1].count('.')
        gs+=sum(a==b=='.' for a,b in zip(w[1:-2],w[2:-1]))
        rows=list(map(''.join,zip(*rows[::-1])))
    return hs,gs

def certificate(rows):
    n=len(rows);h0,g0=rim(rows);r=rows;h,g=h0,g0;sg=0;records=[]
    while len(r)>=61:
        s=len(r);c=[w[3:-3] for w in r[3:-3]];h2,g2=rim(c)
        T=marks(r)-marks(c)
        assert 2*T+h-h2-g-g2<=8*s-13
        j=(n-len(c))//6
        weighted=8*j*n-24*j*j+11*j+h2-h0+g0+g2+2*sg
        cap=weighted//2
        assert marks(rows)-marks(c)<=cap
        records.append((cap+upper(len(c)),cap+comb(len(c)),j))
        sg+=g2;r=c;h,g=h2,g2
    return records

if __name__=='__main__':
    from .comb_cap_transfer import construct
    from .end_band_obstruction import wrapped
    from .crop_end_coupling import locked_fringe
    for n in (103,133):
        for label,r in [('comb',construct(n,4)),('locked',locked_fringe(n)),('wrapped',wrapped(n)),('double',punctures(n,True))]:
            r=verify(r,True);u,step,j=min(certificate(r))
            print(n,label,'best by rim words alone',u,'with smaller comb upper',step,'three-layer bands',j)
