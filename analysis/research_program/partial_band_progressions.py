"""Partial bands of length five and six: cap connectivity and polynomial scores."""
from .zipper_frontier import regular,canonical,step,check
from .repaired_cap_frontier import cap,normalized
from .zipper_rails import build,verify


def cap_test(n,M,r):
    A=regular(n,M);S=A;p=canonical(n,S)
    # Full bands delivered us to the second A row of the final partial band.
    for T in [A|{M+2}]+[A]*(r-3):
        p=step(S,p,T);S=T
    # Both tip rails are now joined. Two regular rows following the
    # center mark suffice to leave the current gap site a fresh singleton.
    a=canonical(n,A)
    for j,x in enumerate(a):
        if x==M+4:a[j]=M
    assert normalized(a)==normalized(p)
    for T in cap(n,M):
        if len(T)==n:assert len(set(p))==n
        p=step(S,p,T);S=T
    assert len(set(p))==1
    print(f'{r}-row ending: tips joined, gap singleton; '
          'singleton penultimate frontier; bottom bar acyclic')


def coefficients(base):
    # All parameters below are affine and the score at most quadratic in t.
    # Evaluate the explicit count expression (not measured forest sizes) at
    # three arguments to check its three Newton coefficients.
    r={23:5,41:6}[base]
    def formulas(t):
        n=base+42*t;k=(base-2)//3+14*t;F=(base-5)//6+7*t
        B=(1 if base==23 else 3)+5*t
        assert n-8-F==7*B+r
        count=(n-2+1+k+1)+F*k+B*(7*(k+1)+1)+(r*(k+1)+1)+(3*k+3+n)
        correction=(23-2*((base-2)//3))//14-2*t
        return count,3*k*k+7*k+correction
    a,b,c=(formulas(t) for t in range(3))
    assert all(x==y for x,y in (a,b,c))
    print(f'n={base}+42t: common Newton coefficients',a[0],b[0]-a[0],c[0]-2*b[0]+a[0])


if __name__=='__main__':
    check(23,12,False)
    for b,r in ((23,5),(41,6)):
        cap_test(23,9,r);coefficients(b)
        for n in (b,b+42,b+84):
            s,e,c,t,f=verify(build(n));k=(n-2)//3
            assert s==f==3*k*k+7*k+(23-2*k)//14
            print(f'side {n}: {s} selected, {e} acyclic forced edges, {c} components, '
                  f'{t} spanning-tree edges, {f} full degree')
