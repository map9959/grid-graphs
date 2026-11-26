"""Join four four-layer corners cyclically, preserving both ends of the slit."""
from functools import lru_cache
from .collar_elbow import canon,corners

def merger(p):
    q=list(p)
    def rt(i):
        while q[i]!=i:i=q[i]
        return i
    def join(i,j):
        i,j=rt(i),rt(j);q[i]=j;return i!=j
    return rt,join

@lru_cache(None)
def segments(kind,old,witness=False):
    # Summary on the four incoming sites and four output sites, with
    # the old-site connections not yet inserted. The seam edges are included.
    out={}
    blocks=corners() if kind else {
        (m,m,canon(p+p)):m.bit_count() for m in range(16)
        for p in [tuple(sum(not (m>>(j-1)&3) for j in range(1,i+1)) for i in range(4))]}
    for (e,b,p),z in blocks.items():
        if old&(e<<1|e>>1):continue
        rt,join=merger([*range(4),*(4+i for i in p)])
        if not all(join(i,4+i) for i in range(4) if (old|e)>>i&1):continue
        key=b,canon([rt(i) for i in (0,1,2,3,8,9,10,11)])
        if key not in out or out[key][0]<z:
            out[key]=z,corners(True)[e,b,p] if kind and witness else b
    return out if witness else {k:w for k,(w,_) in out.items()}

@lru_cache(None)
def compose(p,q):
    rt,join=merger([*p,*(8+i for i in q)])
    if not all(join(4+i,8+i) for i in range(4)):return
    return canon([rt(i) for i in (0,1,2,3,12,13,14,15)])

def apply(d,kind):
    nd={}
    for (old,p),w in d.items():
        for (b,q),v in segments(kind,old).items():
            r=compose(p,q)
            if r:
                k=b,r;nd[k]=max(nd.get(k,w+v),w+v)
    return nd

def straight(d,h):
    for i in range(h):
        e=apply(d,False)
        if len(e)==len(d) and all(e.get(k)==z+2 for k,z in d.items()):
            return {k:z+2*(h-i) for k,z in d.items()},i
        d=e
    return d,h

def closed(n,details=False):
    # Start at the last slice before a corner, so that each turn has a
    # known incoming mask. Two marked innermost arm tips straddling a
    # turn would force a square through the omitted interior vertex.
    best=0;latest=0;winner=None
    for m in range(16):
        p=[sum(not(m>>(j-1)&3) for j in range(1,i+1)) for i in range(4)]
        d={(m,canon(p+p)):m.bit_count()}
        for side in range(4):
            nd={}
            for bit in (0,8):
                group={k:z for k,z in d.items() if k[0]&8==bit}
                after=apply(apply(group,True),False)
                for k,z in after.items():
                    if k[0]&bit:continue
                    nd[k]=max(nd.get(k,z),z)
            d,j=straight(nd,n-9-int(side==3));latest=max(latest,j)
        for (b,p),z in d.items():
            if z<=best:continue
            rt,join=merger(p)
            if all(join(i,i+4) for i in range(4) if (b|m)>>i&1):best=z;winner=m
    return (best,latest,winner) if details else (best,latest)

def witness(n,m,target):
    p=[sum(not(m>>(j-1)&3) for j in range(1,i+1)) for i in range(4)]
    d={(m,canon(p+p),0):(m.bit_count(),())}
    for side in range(4):
        for j in range(n-7-int(side==3)):
            nd={}
            for (a,p,flag),(value,path) in d.items():
                for (b,q),(z,mask) in segments(j==0,a,True).items():
                    if j==1 and flag&b:continue
                    r=compose(p,q)
                    if not r:continue
                    key=b,r,(a&8 if not j else 0)
                    if key not in nd or value+z>nd[key][0]:nd[key]=value+z,path+(mask,)
            d=nd
    for (b,p,_),(z,path) in d.items():
        _,join=merger(p)
        if z!=target or not all(join(i,i+4) for i in range(4) if (m|b)>>i&1):continue
        marks=set();p0=0;arms=[]
        for side in range(4):
            def cell(y,x):
                for _ in range(side):y,x=n-1-x,y
                return y,x
            # Start at top left, coming from the east and exiting south.
            # Rotation counterclockwise takes top left to bottom left.
            corner=path[p0];p0+=1
            marks.update(cell(i//4,i%4) for i in range(16) if corner>>i&1)
            length=n-8-int(side==3)
            arm=path[p0:p0+length]+((m,) if side==3 else ());p0+=length
            arms.append(arm)
            marks.update(cell(y+4,x) for y,a in enumerate(arm) for x in range(4) if a>>x&1)
        rows=[''.join('#' if (y,x) in marks else '.' for x in range(n)) for y in range(n)]
        return rows,arms
    raise AssertionError

if __name__=='__main__':
    from .extend_forest_28 import verify
    n=20;best,j,m=closed(n,True)
    assert best==8*n-40 and j<n-10
    rows,arms=witness(n,m,best)
    assert verify(rows)[0]==best
    print('closed four-layer collar:',best,'at side',n,'latest straight repeat',j,'tree',verify(rows))
    for side in (18,19):assert closed(side)[0]==8*side-40
    assert rows[9]==rows[10] and all(s[9]==s[10] for s in rows)
    def pump(n):
        r=rows[:10]+[rows[9]]*(n-20)+rows[10:]
        return [s[:10]+s[9]*(n-20)+s[10:] for s in r]
    tree=verify(pump(103));assert tree[0]==8*103-40
    print('all sides >=20: optimum 8n-40; pumped physical collar at 103',tree)
