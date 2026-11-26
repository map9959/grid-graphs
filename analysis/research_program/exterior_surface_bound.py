"""Geometry-only upper on the pitch-frame exterior functional, independent of its filling."""
from fractions import Fraction as Q
from math import ceil
from functools import lru_cache
from .frame_exterior import audit,construct
from .wired_strip_flow import advance

@lru_cache(None)
def wing_opts(w,old,p):
    return [(v,z[2],v.bit_count()) for v in range(1<<w)
            if (z:=advance(w,(0,old,p),v,False)) is not None]

def vectors(d):
    w=d-1;dp={(-1,tuple(range(w+1))):0}
    while True:
        nxt={}
        for (old,p),v in dp.items():
            for b,q,c in wing_opts(w,old,p):
                key=b,q;nxt[key]=max(nxt.get(key,0),v+c)
        dp=nxt
        yield dp

@lru_cache(None)
def wing_marks(d,H):
    """Exact finite full-bar strip optimum; first free line is blank."""
    if d==1:return 0
    from itertools import islice
    return max(next(islice(vectors(d),H-1,None)).values())

def pump(d,slope,offset):
    seen={}
    for H,dp in enumerate(vectors(d),1):
        v=max(dp.values());assert v<=slope*H+offset
        sig=frozenset((s,z-v) for s,z in dp.items())
        if sig in seen:
            k,z=seen[sig];assert v-z==(H-k)*slope
            print('wing',d,'identical normalized vectors at',k,H,'gain',v-z)
            return
        seen[sig]=H,v
        assert H<100

def pack(pins):
    # Dynamic programming on the internal pitch columns only. Each
    # disjoint group of 2 or 3 full triples pays (#pins-1)_+.
    vals=[0]
    for i in range(1,len(pins)+1):
        vals.append(max([vals[-1]]+[vals[i-k]+max(0,sum(pins[i-k:i])-1)
                                      for k in (2,3) if k<=i]))
    return vals[-1]

def price(n,box,s,pins=None):
    a,b,l,r=box;H=b-a+1;W=r-l+1
    assert 0<a<b<n-1 and 0<l<r<n-1 and W%3==1 and 2<=s<=(W+2)//3
    ds=(l,n-1-r)
    m=(W+2)//3-2
    coupon=max(0,s-2-ceil(Q(m,3))) # partition all m into blocks of at most three
    if pins is not None:
        assert len(pins)==m and sum(pins)==s-2
        coupon=pack(pins)
    # Two chains of intersecting three-tooth windows on the complete
    # end word. With the exterior lateral leaf of each side tooth as
    # the last site of its triple, both extreme pins are included.
    chain=ceil(Q(2*(s-1),3))
    # Allocate disjoint exterior debits. If a wing is used for its
    # surface tariff, do not charge any of its runs to the area bound.
    # A charged wing run is wholly contained in its wing; its stars
    # cannot enter the *remote* opposite wing.
    best=0
    for mask in range(4):
        debit=0;remote=0
        for i,d in enumerate(ds):
            if mask>>i&1:
                delta=(0,Q(31,210),Q(1,10))[d%3]
                max_marks=((H+2)*(Q(d,3)-delta)).__floor__()
                if d<=8:max_marks=min(max_marks,wing_marks(d,H))
                debit+=max(0,d*H-3*max_marks-2*d,
                           H if d==1 else H-2 if d==2 else 0)
            else:remote+=d-1
        area=ceil(Q((H-2)*remote,3*n))
        # The larger window can use top/bottom corner-neighbor holes
        # when the corresponding side margin is <=2.
        corner_loss=sum((2-int(a==1 and mask>>i&1)-int(b==n-2 and mask>>i&1))
                        for i,d in enumerate(ds) if d<=2)
        debit+=max(ceil(Q(remote,3)),coupon+area,chain+area-corner_loss)
        # Don't double-charge a corner whose vertical neighbor was
        # counted already in the side interval's missing incidences.
        debit+=4-mask.bit_count()*(int(a==1)+int(b==n-2))
        best=max(best,debit)
    return 4*n-s-best

if __name__=='__main__':
    pump(4,1,2);pump(5,Q(3,2),3)
    for n in (43,73,103):
        rows=construct(n,4)
        for box in ((3,n-10,3,n-4),(3,n-10,4+2,n-7),(3,n-10,3,n-7)):
            s,_,_,_,_,actual,_=audit(rows,box)
            F=price(n,box,s)
            assert audit(rows,box,ledger=True)<=F and 3*actual<=n*n+F-1
            print(n,box,'pins',s,'geometry-only F <=',F,'score <=',(n*n+F-1)//3)
    for d in (1,2,4,5,7):
        n=103;H=88;W=n-2*d-(n-2*d-1)%3
        box=(6,6+H-1,d,d+W-1);s=(W+2)//3
        F=price(n,box,s)
        print('103 hypothetical frame',box,'pins',s,'score <=',(n*n+F-1)//3)
    for s in (2,10,20,32):
        # The only dependence on vertical placement is the corner debit;
        # an extreme placement gives the weaker price.
        H=1+max(h for h in range(2,102) if (103**2+price(103,(1,h,4,97),s)-1)//3>3646)
        print('103 margins 4,5;',s,'pins: 3647 excluded at every height >=',H)
    from .extend_forest_28 import verify
    base=construct(100,4)
    rows=['.'+row+'.'+('#' if i%3==0 else '.') for i,row in
          enumerate(base[:4]+[base[3]]*3+base[4:])]
    box=(6,90,4,97);s,*_=audit(rows,box)
    measured=audit(rows,box,ledger=True);F=price(103,box,s);tree=verify(rows)
    assert measured<=F and 3*tree[0]<=103**2+F-1
    print('off-phase physical check: pins',s,'F',measured,'<=',F,'tree',tree)
