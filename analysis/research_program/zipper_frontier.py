"""Replay the two finite middle/cap transitions in the zipper induction."""
def regular(n,L):
    return set(range(0,L+1,3))|set(range(L+4,n,3))


def canonical(n,S):
    # Every marked site is in its own component with its immediate
    # horizontal neighbors; uncovered sites are singletons.
    a=list(range(n))
    for s in S:
        for x in range(max(0,s-1),min(n,s+2)):a[x]=s
    return a


def step(S,part,T):
    n=len(part);p=list(part)+list(range(n,2*n))
    def root(x):
        while p[x]!=x:x=p[x]
        return x
    def edge(x,y):
        a,b=root(x),root(y)
        assert a!=b,'cycle'
        p[a]=b
    for j in range(n):
        if j in S or j in T:edge(j,n+j)
        if j and (j in T or j-1 in T):edge(n+j-1,n+j)
    roots=[root(n+j) for j in range(n)]
    return [roots.index(r) for r in roots]


def check(n,L,cap):
    S=regular(n,L);a=canonical(n,S);A=S.copy()
    seq=[A|{L+2},A,A,(A-{L})|{L+2},(A-{L})|{L-1}]
    B=regular(n,L-3)
    if cap:
        M=L-3
        for offsets in ((2,),(-4,-3,-2,-1),(1,)):
            seq.append(set(range(0,M-5,3))|{M+d for d in offsets}|set(range(M+4,n,3)))
        seq += [set(),set(range(n))]
    else:seq += [B,B]
    for T in seq:
        if cap and len(T)==n:assert len(set(a))==n
        a=step(S,a,T);S=T
    if not cap:
        b=canonical(n,B)
        assert a==[b.index(r) for r in b]
    return len(seq)


if __name__=='__main__':
    for cap in (False,True):
        print('cap' if cap else 'middle','rows checked without cycle',check(23,12,cap))
