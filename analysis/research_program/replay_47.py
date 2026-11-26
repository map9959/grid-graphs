"""Check both whole forests and the physical frontier after the two waiting rows."""
from .repair_53 import repaired,verify,parameters
from .zipper_frontier import step,canonical,regular
from .repaired_cap_frontier import normalized


def replay(n):
    rows=repaired(n);k=(n-2)//3
    F=(n-5)//6;extra,M=parameters(n);end=F+4+extra
    S=set();a=list(range(n))
    for i,row in enumerate(rows):
        T={j for j,ch in enumerate(row) if ch=='#'}
        a=step(S,a,T);S=T
        if F+4<=i<=end or (end<i<=n-6 and (i-end)%7==0):
            L=3*F-3*max(0,(i-end)//7)
            assert S==regular(n,L)
            want=[0 if x==M else x for x in canonical(n,S)]
            assert normalized(a)==normalized(want)
        if i==n-2:assert len(set(a))==n
    s,e,c,edges,f=verify(rows)
    upper=3*k*k+7*k+(23-2*k)//14
    assert s==f==upper
    print(f'{n}: only extra rail connection 0~{M}; pre-bottom singletons {n}; '
          f'{e} forced edges, {c} components, {edges} tree edges, full degree {f} = upper')


if __name__=='__main__':
    import sys
    for n in map(int,sys.argv[1:] or (47,89)):replay(n)
