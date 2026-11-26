"""Read a doubled diagonal cylinder in normal slices d=r-c modulo (12,12)."""
from .temperley_diagonal import saturated

WIDTH=12
FULL=(1<<WIDTH)-1


def transitions(occupied):
    """Enumerate every disjoint matching from free sites to the next slice.

    Return vertical and horizontal source masks; vertical preserves c,
    horizontal uses c-1 in the next slice.
    """
    free=FULL^occupied
    ver=free
    while True:
        hor=free^ver
        shift=(hor>>1)|((hor&1)<<(WIDTH-1))
        if not ver&shift:
            yield ver,hor,ver|shift
        if not ver:
            break
        ver=(ver-1)&free


def cross(tile,d):
    v=h=0
    for c in range(WIDTH):
        pair=tile[(d+c)%WIDTH,c]
        if pair==(1,0):v|=1<<c
        if pair==(0,-1):h|=1<<c
    return v,h


def mid(incoming_vertical,outgoing_vertical):
    # On an odd normal slice an even column midpoint is on a vertical
    # primal edge, whereas an odd column midpoint is on a horizontal one.
    return (incoming_vertical|outgoing_vertical)^0xaaa


def centers(prev,nxt):
    return sum(1 for c in range(0,WIDTH,2)
               if all(mask>>(j%WIDTH)&1 for mask,j in
                      ((prev,c),(prev,c+1),(nxt,c),(nxt,c-1))))


def audit_flux(tile):
    """Verify the finite-strip endpoint/flux identity, including both cut signs."""
    vertices={(i,j) for i in range(6) for j in range(6)}
    arrows={}
    for i,j in vertices:
        x,y=tile[2*i,2*j]
        arrows[i,j]=((i+x)%6,(j+y)%6)
    edges={frozenset((p,q)) for p,q in arrows.items()}
    F={p for p in vertices if sum(p in e for e in edges)==4}
    ff={e for e in edges if e<=F}
    for h in range(1,6):
        S={p for p in vertices if (p[0]-p[1])%6<h}
        terminal=sum(2-sum(p in e for e in ff) for p in S&F)
        waste=sum(p in S and p not in F and q not in F for p,q in arrows.items())
        flux=sum((int(q in S)-int(p in S))*(1 if p in F else 2)
                 for p,q in arrows.items() if q in F)
        assert 6*len(F&S)==2*len(S)+flux-terminal-2*waste


def band_flux_bound(lo,hi,a,b,*,ledger=False,expected=None):
    """Analytic upper on the 66 mutable score bits per longitudinal repeat.

    Normal coordinate is i-j in primal sites, not in template tiles.
    Choose cuts far enough out that all labels of crossing arrows are fixed.
    """
    def tile(r,c):
        k=(r-a)//6-(c-b)//6
        return lo if k < -1 else hi if k > 1 else None
    def isfull(i,j):
        for x,y in ((1,0),(-1,0),(0,1),(0,-1)):
            r,c=2*i+x,2*j+y
            t=tile(r,c)
            assert t is not None
            if (r+t[r%12,c%12][0])%2:
                return False
        return True
    L,R=-12,12
    flux=known=mutable=all_flux=0
    for d in range(L-1,R+2):
        for j in range(6):
            i=j+d
            if L<=d<=R:
                if any(tile(2*i+x,2*j+y) is None for x,y in ((1,0),(0,1),(-1,0),(0,-1))):
                    mutable+=1
                else:
                    known+=isfull(i,j)
            if d not in (L-1,L,R,R+1):
                continue
            t=tile(2*i,2*j)
            x,y=t[(2*i)%12,(2*j)%12]
            delta=int(L<=d+x-y<=R)-int(L<=d<=R)
            all_flux+=delta
            if delta and isfull(i+x,j+y):
                flux+=delta*(1 if isfull(i,j) else 2)
    if expected is not None:
        assert mutable==expected,(mutable,expected)
    def rails(t):
        labels=set()
        for i in range(6):
            for j in range(6):
                if all((2*i+x+t[(2*i+x)%12,(2*j+y)%12][0])%2==0
                       for x,y in ((1,0),(0,1),(-1,0),(0,-1))):
                    x,y=t[2*i,2*j]
                    labels.add((bool(y),i if y else j))
        assert len(labels)==2
        return labels
    # Each unmatched incident rail has an endpoint in S: an FF path
    # cannot bend. Arrow orientations are not additional endpoint labels.
    unmatched=len(rails(lo)^rails(hi))
    if ledger:
        return 6*(R-L+1)+all_flux-3*known
    return (12*(R-L+1)+flux-unmatched)//6-known


def check():
    checked=0
    for tile in saturated():
        cuts=[cross(tile,d) for d in range(WIDTH)]
        masks={}
        for d,(v,h) in enumerate(cuts):
            pv,ph=cuts[d-1]
            occ=pv|(ph>>1)|((ph&1)<<(WIDTH-1))
            assert any((v,h)==(a,b) for a,b,_ in transitions(occ))
            if d%2:masks[d]=mid(pv,v)
        score=sum(centers(masks[(d-1)%WIDTH],masks[d+1]) for d in range(0,WIDTH,2))
        assert score==12
        audit_flux(tile)
        # A flippable square gives a second tiling, usually unsaturated.
        for i in range(11):
            for j in range(11):
                if tile[i,j]==tile[i+1,j]==(0,1):
                    alt=tile.copy()
                    for k in (j,j+1):
                        alt[i,k],alt[i+1,k]=(1,0),(-1,0)
                    audit_flux(alt)
                    break
            else:
                continue
            break
        checked+=1
    print("saturated layouts:",checked,"slice transitions replayed:",WIDTH*checked,
          "preserved per primal 6x6 cell:",12)


if __name__=="__main__":
    check()
