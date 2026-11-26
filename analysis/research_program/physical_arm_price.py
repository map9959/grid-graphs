"""Free one entire ten-site-wide arm and the strict core, fixing the other collar sites."""
import subprocess
from .comb_cap_transfer import construct
from .sparse_component_exchange import Forest


def price(rows):
    n=len(rows); d=9; s=n-2*d; m=s-2
    depth=lambda i,j:min(i,j,n-1-i,n-1-j)
    D={(i,j) for i in range(n) for j in range(n) if depth(i,j)<=d
       and not (i<=d and d<j<n-1-d)}
    F=Forest(n)
    marked=lambda p:rows[p[0]][p[1]]=='#'
    rim={p for p in D if depth(*p)==d}
    gaps=0
    for i,j in D:
        for q in ((i+1,j),(i,j+1)):
            if q not in D:continue
            if marked((i,j)) or marked(q):assert F.join((i,j),q)
            elif (i,j) in rim and q in rim:gaps+=1
    flagged={F.root(p) for p in rim}
    fixed=(12*sum(map(marked,D-rim))-4*sum(not marked(p) for p in rim)
           -4*gaps+6*len(flagged))
    # K is the number of marked core corners (see radial ledger).
    corners=[(i,j) for i in (d,n-1-d) for j in (d,n-1-d)]
    fixed+=3*sum(map(marked,corners))
    args=[];ends=[]
    for j in (d,n-1-d):
        col=[(i,j) for i in range(d+1)]; roots=list(map(F.root,col));ends.append(roots)
        args.extend([sum(marked(p)<<i for i,p in enumerate(col)),
                     ''.join(str(roots.index(r)) for r in roots),
                     sum((r in flagged)<<i for i,r in enumerate(roots))])
    shared=set(ends[0])&set(ends[1])
    assert len(shared)<=1 and shared<=flagged
    args.extend([sum((r in shared)<<i for i,r in enumerate(ends[0])),
                 ends[1].index(next(iter(shared))) if shared else 0])
    variable=int(subprocess.check_output(['target/radial_outer_strip','9','4',str(m),*map(str,args)]))
    score=(4*s*s+14*s-18+fixed+4*d*m+variable)//12
    assert score>=sum(r.count('#') for r in rows)
    return variable,score


if __name__=='__main__':
    r=construct(103,4)
    for _ in range(4):
        print(price(r),flush=True)
        r=[''.join(col) for col in zip(*r[::-1])]
