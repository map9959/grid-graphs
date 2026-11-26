"""Exact bound for all replacements of the last forty rows of the side-53 zipper."""
from fractions import Fraction as Q
from .square_dual_physical import inspect,stencil,json
from .zipper_rails import build


def bound(n=53):
    h,threshold={53:(13,985),77:(17,2048),119:(24,4832)}[n]
    upper,_=inspect(n,physical_costs=True)
    ys=[Q(q) for key,q in json.loads(stencil(2).read_text()) if key[0]=='corner']
    assert ys==[-Q(9,14)]
    # Inspect only edges both of whose vertices are in the fixed prefix.
    rows=build(n)[:h];p=list(range(len(rows)*n))
    def root(u):
        while p[u]!=u:u=p[u]
        return u
    for i,row in enumerate(rows):
        for j in range(n):
            u=i*n+j
            for ok,v in ((i>0,u-n),(j>0,u-1)):
                if ok and '#' in (row[j],rows[v//n][v%n]):p[root(u)]=root(v)
    assert all(root(u)!=root(0) for u in range((h-1)*n,h*n))
    assert root(n-1)!=root(0)
    # No edge introduced by changing rows 13..52 can touch that component.
    # Choose roots at two corners in distinct components, then D4-average.
    # The RHS for the single weighted corner row increases from 1 to >=2.
    result=upper+ys[0]
    assert result<threshold
    print('sealed top-left component after',h,'rows; two corner sinks; exact prefix upper',result,'<',threshold)


if __name__=='__main__':
    import sys
    bound(int(sys.argv[1]) if len(sys.argv)>1 else 53)
