"""Check the interfaces used to shorten the fixed (59,59) junction domain."""
from .shared_root_pump import check
from .exit_pump import tables

def section(n,j):
    # At a cut beyond column 61 the fixed NW band is absent.
    assert 61<j<n-7
    return [*range(7),*range(57,62),*range(n-7,n)]

def run():
    L=check(7,42);K=check(5,42,True,57)
    for n in (119,161):
        typ=tables(n)[0];base=tables(119)[0]
        for j in range(68,71+max(K,L)+n-119):
            assert section(n,j)==section(n,69)
            for t in (0,1):
                for r in [*range(7-2*t),*range(57,62-2*t)]:
                    assert typ(t,r,j)==base(t,r,12+(j-12)%3)
    assert 69+max(K,L)+2<119-7
    print('cut at 69: side / interior / side sections 7 / 5 / 7; transposed cuts identical')

if __name__=='__main__':run()
