"""Compare the boundary strip charge, a physical replacement, and the unrestricted gap."""
from .phase_length_exchange import puncture,holes
from .comb_cap_transfer import construct
from .extend_forest_28 import verify

def audit(rows,d,lo,hi):
    n=len(rows);H=hi-lo;l=d//3;assert d==3*l and d>=3 and d<n and 0<=lo<hi<=n
    strip=[r[:d+1] for r in rows[lo:hi]];ideal='#..'*l+'#'
    M=sum(r[:d].count('#') for r in strip);J=sum(r[d]=='.' for r in strip)
    B=sum(r!=ideal for r in strip);B0=sum(r[:d]!=ideal[:d] for r in strip)
    outer=sum(r[0]=='.' for r in strip);I=strip[0].count('#')+strip[-1].count('#')
    R=sum(c=='#' and (not x or r[x-1]=='.') and (not y or strip[y-1][x]=='.')
          for y,r in enumerate(strip) for x,c in enumerate(r))
    c=H*(d+1)-sum((r[x]=='#' or r[u]=='#') for r in strip for x,u in zip(range(d),range(1,d+1)))-sum(
        (a=='#' or b=='#') for r,t in zip(strip,strip[1:]) for a,b in zip(r,t))
    assert 3*(M-l*H)==2*J-outer+I-R-c and B<=3*R+c
    # Clear both seam rows at one end and one at the other. On the
    # physical full side there are no attachments at either end.
    start=lo+int(lo>0);stop=hi-2*int(hi<n)
    new=[r if not lo<=y<hi else (ideal[:d] if start<=y<stop else '.'*d)+r[d:]
         for y,r in enumerate(rows)]
    t=verify(new);delta=t[0]-sum(r.count('#') for r in rows)
    assert delta==l*max(0,stop-start)-M
    if d in (3,6):
        a,b,C=(10,20,70) if d==3 else (6,24,126)
        debit=a*B0-b*J-C-30*l*(H-max(0,stop-start))
        assert 30*delta>=debit
        k=n//3;r=(3*k-13)%10
        print(n,'depth',d,'B',B0,'J',J,'30 x certified gain',debit,
              'needed >',k-26+3*r,'physical gain',delta,'tree',t)
    return new

def witnesses(n):
    rows=construct(n,4)
    near=puncture(rows,n//2,2)
    assert all(holes(near))
    for d in (3,6):audit(near,d,0,n)
    many=rows
    for y in range(15,n-9,9):many=puncture(many,y,2)
    assert all(holes(many))
    for d in (3,6):audit(many,d,0,n)
    audit(many,9,11,n-13)

if __name__=='__main__':
    witnesses(193)
