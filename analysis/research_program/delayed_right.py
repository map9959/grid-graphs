"""Even-k residue-two zipper: delay only the last right-front advance."""
from .zipper_rails import build,verify
from .zipper_frontier import canonical,regular,step
from .repaired_cap_frontier import cap,normalized


def config(n):
    base=38+(n-38)%42
    assert base in (38,44,50,56,62,68,74) and n>=base
    F=(n-2)//6;e={38:1,56:2}.get(base,0)
    B,h=divmod(n-8-F-e,7)
    return F,e,B,h


def repaired(n):
    F,e,_,_=config(n)
    rows=list(map(list,build(n,delay=F-1,side='right',extra=e)))
    rows[0][1]='.';rows[1][0]='#'
    for a in range(F+1):
        rows[a+2][3*a]='#'
        if a<F:rows[a+2][3*a+2]='.'
    return list(map(''.join,rows))


def terminal(h):
    n=23;L=12;A=regular(n,L);M=L-3;D=regular(n,M)
    seq=[A|{L+2},A,A,(A-{L})|{L+2},(A-{L})|{L-1}]
    seq += [D|{M+2} if i==2 else D for i in range(h)]
    S=A;p=canonical(n,S)
    for T in seq+cap(n,M):
        if len(T)==n:assert len(set(p))==n
        p=step(S,p,T);S=T
    print('partial rows',h,'cap acyclic, singleton penultimate frontier')


def physical(n):
    F,e,B,h=config(n);rows=repaired(n);p=list(range(n));S=set()
    for i,row in enumerate(rows):
        T={j for j,x in enumerate(row) if x=='#'};p=step(S,p,T);S=T
        # Check every complete band's input invariant, and waiting rows.
        if F+4<=i<=F+4+e or (F+4+e<i<=F+4+e+7*(B-1) and (i-F-4-e)%7==0):
            L=3*(F-max(0,(i-F-4-e)//7))
            assert T==regular(n,L) and normalized(p)==normalized(canonical(n,T))
        if i==n-2:assert len(set(p))==n
    s,edges,c,tree,f=verify(rows);k=(n-2)//3;upper=3*k*k+7*k+(23-2*k)//14
    assert s==f==upper-int((n-56)%42==0)
    print(f'side {n}: canonical rail frontier; {edges} acyclic forced edges, '
          f'{c} components, {tree} tree edges, {f} full degree, upper {upper}')


if __name__=='__main__':
    import sys
    for n in map(int,sys.argv[1:] or (44,86)):
        terminal(config(n)[-1]);physical(n)
