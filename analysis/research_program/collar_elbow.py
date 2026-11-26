"""Free-ended L-shaped four-layer quarter collar, incl. the physical corner."""
from functools import lru_cache

def canon(p):
    return tuple(p.index(x) for x in p)

@lru_cache(None)
def step(s,v):
    old,p=s
    q=[*p,4,5,6,7]
    def root(i):
        while q[i]!=i:i=q[i]
        return i
    def join(i,j):
        i,j=root(i),root(j);q[i]=j;return i!=j
    if any((old|v)>>i&1 and not join(i,i+4) for i in range(4)):return
    if any(v>>i&3 and not join(i+4,i+5) for i in range(3)):return
    return v,canon([root(i) for i in range(4,8)])

def run(d,length):
    for _ in range(length):
        nd={}
        for s,w in d.items():
            for v in range(16):
                key=step(s,v);cost=w+v.bit_count()
                if key:nd[key]=max(nd.get(key,cost),cost)
        d=nd
    return d

def arm(length):
    return run({(0,(0,1,2,3)):0},length)

@lru_cache(None)
def corners(witness=False):
    # A 4x4 corner interfaces with the east and south arms. Retain
    # eight actual first-arm sites as terminals, joined to this patch
    # if either incident endpoint is marked (accounted for below).
    from .sparse_component_exchange import Forest
    out={}
    for m in range(1<<16):
        F=Forest(4)
        if not all(F.join((y,x),(u,v)) for y in range(4) for x in range(4)
                   for u,v in ((y+1,x),(y,x+1)) if u<4 and v<4 and
                   (m>>(4*y+x)|m>>(4*u+v))&1):continue
        e=sum((m>>(4*y+3)&1)<<y for y in range(4))
        s=m>>12
        p=canon([F.root((i,3)) for i in range(4)]+[F.root((3,i)) for i in range(4)])
        k=e,s,p
        if k not in out or out[k].bit_count()<m.bit_count():out[k]=m
    return out if witness else {k:m.bit_count() for k,m in out.items()}

def elbow(h,v):
    east,south=arm(h),arm(v);best=0
    for (e,s,p),cost in corners().items():
        for (a,pa),wa in east.items():
            if a&(e<<1|e>>1):continue
            for (b,pb),wb in south.items():
                z=cost+wa+wb
                if z<=best or b&(s<<1|s>>1):continue
                q=[*p,*(8+i for i in pa),*(12+i for i in pb)]
                def rt(i):
                    while q[i]!=i:i=q[i]
                    return i
                def join(i,j):
                    i,j=rt(i),rt(j);q[i]=j;return i!=j
                if all(join(i,i+8) for i in range(8) if
                       ((e|a)|((s|b)<<4))>>i&1):best=z
    return best

if __name__=='__main__':
    d=arm(5)
    assert run(d,1)=={s:z+2 for s,z in d.items()}
    assert elbow(5,5)==27
    print('arm lengths 5 -> 6:',len(d),'full state prices recur with shift 2; elbow(5,5) = 27')
    print('all h,v >= 5: 2(h+v)+7; all square sides >= 18: four layers <= 8n-36')
