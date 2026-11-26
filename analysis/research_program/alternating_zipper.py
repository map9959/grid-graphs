"""Side-56 SAT repair, written in transposed coordinates as alternating zipper bands."""
from pathlib import Path
from .zipper_frontier import regular,canonical,step
from .repaired_cap_frontier import normalized
from .extend_forest_28 import verify


def roof(n,L):
    return [set(range(0,L+1,3))|s for s in
            ({L+2,n-1},set(range(L+5,n-2))|{n-1},{L+3,n-1})]+[{0},set(range(n))-{1}]


def local():
    for right in (False,True):
        n=26;L=12;A=regular(n,L);B=regular(n,L+(3 if right else -3))
        S=A;p=canonical(n,A)
        for T in (A|{L+2},A,A,(A-{L+4 if right else L})|{L+2},
                  (A-{L+4 if right else L})|{L+5 if right else L-1},B,B):
            p=step(S,p,T);S=T
        assert normalized(p)==normalized(canonical(n,B))
    S=A;p=canonical(n,A)
    for T in [A|{L+2},A,A]+roof(n,L):
        p=step(S,p,T);S=T
        if T=={0}:assert normalized(p)==[0,0,*range(2,n)]
    print('left and right complete bands restore canonical partition; partial band and wide cap acyclic')


def rows(n):
    assert n>=56 and (n-56)%42==0
    F=(n-2)//6
    seq=[set(range(3,n))|{0},{0}]
    for h in range(F):
        seq.append({0}|set(range(0,3*h,3))|set(range(2+3*h,n-5-3*h,3))|set(range(n-1-3*h,n,3)))
    L=3*(F-1);B,h=divmod(n-7-F,7)
    assert h==5
    for b in range(B):
        A=regular(n,L);right=b%2==0
        seq.extend([A,A,A|{L+2},A,A,(A-{L+4 if right else L})|{L+2},
                    (A-{L+4 if right else L})|{L+5 if right else L-1}])
        L+=3 if right else -3
    A=regular(n,L)
    return seq+[A,A,A|{L+2},A,A]+roof(n,L)


def replay(n):
    F=(n-2)//6;seq=rows(n);assert len(seq)==n
    r=[''.join('#' if j in T else '.' for j in range(n)) for T in seq]
    if n==56:
        assert r==[''.join(s) for s in zip(*Path(__file__).with_name('forest_56.txt').read_text().splitlines())]
    S=set();p=list(range(n));L=3*(F-1)
    for i,T in enumerate(seq):
        p=step(S,p,T);S=T
        if F+3<=i<=n-6 and (i-F-3)%7==0:
            assert T==regular(n,L) and normalized(p)==normalized(canonical(n,T))
            L+=3 if ((i-F-3)//7)%2==0 else -3
        if i==n-6:
            M=max(x for x in T if x%3==0)
            want=[M if x==M+4 else x for x in canonical(n,T)]
            assert normalized(p)==normalized(want)
        if i==n-2:assert normalized(p)==[0,0,*range(2,n)]
    s,e,c,t,f=verify(r);k=(n-2)//3
    assert s==f==3*k*k+7*k+(23-2*k)//14
    print(f'side {n}: canonical band starts; final tips joined; penultimate frontier only 0~1; '
          f'{s} selected, {e} acyclic forced edges, {c} components, {t} tree edges, full degree {f} = upper')


if __name__=='__main__':
    import sys
    local()
    for n in map(int,sys.argv[1:] or (56,98)):replay(n)
