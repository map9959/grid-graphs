"""Expand the side-41 witness into two converging fronts and a drifting seven-row band."""
from .extend_forest_23 import old,verify


def build(n,delay=None,side='right',extra=0):
    assert (n==23 or n>=38) and n%3==2
    def grid(S):return ''.join('#' if j in S else '.' for j in range(n))
    rows=[grid(set(range(n-3))|{n-1}),grid({n-1}),grid(set(range(2,n-1,3))|{n-1})]
    L=0;R=n-1;step=0
    while R-L>4:
        rows.append(grid(set(range(0,L+1,3))|set(range(L+5,R-4,3))|set(range(R,n,3))))
        if step!=delay or side!='left':L+=3
        if step!=delay or side!='right':R-=3
        step+=1
    assert R-L==4
    for _ in range(extra):
        rows.append(grid(set(range(0,L+1,3))|set(range(L+4,n,3))))
    while len(rows)<n-5:
        s=set(range(0,L+1,3))|set(range(L+4,n,3))
        rem=n-5-len(rows)
        for phase in range(min(7,rem)):
            if phase==2:q=s|{L+2}
            elif rem>=7 and phase>=5:q=(s-{L})|{L+2 if phase==5 else L-1}
            else:q=s
            rows.append(grid(q))
        if rem>=7:L-=3
    assert L>=6
    for offsets in ((2,),(-4,-3,-2,-1),(1,)):
        rows.append(grid(set(range(0,L-5,3))|{L+d for d in offsets}|set(range(L+4,n,3))))
    return rows+['.'*n,'#'*n]


if __name__=='__main__':
    assert build(41)==old(41)
    for n in (41,53,59,65,77,83,101,143):
        k=(n-2)//3;v=verify(build(n))
        upper=3*k*k+7*k+(23-2*k)//14
        print(n,'selected,forced,components,tree,full',v,'certified upper',upper)
