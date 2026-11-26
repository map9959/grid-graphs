"""Replay a diagonally advancing stack of coupled, inexpensive rooted strips."""
import gzip,json
from pathlib import Path
from .tile_family_lp import typ

def row(k,q):
    # q counts tile rows up from the south edge. Both margin masks are
    # clipped to remove the physical depth-one sites.
    p=((3,8,264),(33,32,384),(16,16))[q%3]
    s=k-2-q%3-4*(q//3)
    assert s>=1
    w=[7]*s+list(p)+[448]*k;w=w[:k];w[0]&=438;w[-1]&=219
    return s,w

def push(front,m,teeth):
    old,pp=front;N=len(m);p=list(pp)+list(range(N+1,2*N+1))
    def root(x):
        while p[x]!=x:p[x]=p[p[x]];x=p[x]
        return x
    def edge(x,y):
        a,b=root(x),root(y);assert a!=b,'forced cycle';p[a]=b
    for j,b in enumerate(m):
        x=N+1+j
        if j and (b or m[j-1]):edge(x-1,x)
        if old and (old[j] or b):edge(j,x)
        if b and j in teeth:edge(x,N)
    ids={root(N):N}
    return m,[ids.setdefault(root(N+1+j),j) for j in range(N)]+[N]

def group(k,a,B,front):
    K=k-1;N=3*k;s=k-4-4*a;assert s>=12
    prev=row(k,3*a-1)[1] if a else None
    for q in range(3*a,3*a+3):
        s,w=row(k,q);i=k-1-q
        # Check both deep axes, including every square straddling a strip seam.
        for j,m in enumerate(w):
            if min(i,j,k-1-i,k-1-j)>=4:assert not(m&16 and m&170)
        if prev:
            for j in range(K):
                assert (w[j],w[j+1],prev[j],prev[j+1]) in B[typ(i,K),typ(j,K)]
        for lane in (2,1,0):
            m=[bool(v&(1<<(3*lane+b))) for v in w for b in range(3)]
            front=push(front,m,range(N) if q==0 and lane==1 else (1,N-2))
        assert sum(3-v.bit_count() for v in w)==(4 if q==0 else 6)
        prev=w
    assert front==interface(k,3*a+2)
    return front

def interface(k,q):
    N=3*k
    if q<0:return None,list(range(N+1))
    s,w=row(k,q)
    m=[bool(v&(1<<b)) for v in w for b in range(3)]
    return m,[N if j<3*s+2 else j for j in range(N)]+[N]

def main():
    B={(u,v):set(map(tuple,ws)) for u,v,ws in json.loads(gzip.decompress(
        Path('target/tile_family_3_5_h6.json.gz').read_bytes()))}
    # The four finite gadgets after contracting homogeneous margins.
    for a in range(4):
        k=12+4+4*a
        group(k,a,B,interface(k,3*a-1))
        print('group',a,'west length 12, east span',k-12,'interface verified')
    for k in (39,53,67,81):
        groups=2*((k-12)//8)
        front=interface(k,-1)
        for a in range(groups):front=group(k,a,B,front)
        print('tile width',k,'joint cheap strips',3*groups//2,'deficit',18*groups-2)

if __name__=='__main__':main()
