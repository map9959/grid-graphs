"""Two representative frontier calculations for the nontrivial prefix wire."""
from .zipper_frontier import canonical,regular,step


def normalized(a):
    return [a.index(v) for v in a]


def cap(n,M):
    return [set(range(0,M-5,3))|{M+d for d in offsets}|set(range(M+4,n,3))
            for offsets in ((2,),(-4,-3,-2,-1),(1,))]+[set(),set(range(n))]


def check():
    # Direct representative with the wire incident to its closest possible
    # left rail M=L-3. The middle induction in the text also handles M<L-3.
    n=23;M=9;L=M+3
    S=regular(n,L);a=canonical(n,S);a=[0 if x==M else x for x in a]
    A=S.copy();B=regular(n,M)
    for T in (A|{L+2},A,A,(A-{L})|{L+2},(A-{L})|{L-1},B,B):
        a=step(S,a,T);S=T
    assert normalized(a)==normalized([0 if x==M else x for x in canonical(n,B)])
    print('7 middle rows: no cycle; output canonical except rail 0 joined to rail M')
    for T in cap(n,M):
        if len(T)==n:assert len(set(a))==n
        a=step(S,a,T);S=T
    print('5 cap rows: no cycle; pre-bottom frontier consists entirely of singletons')


if __name__=='__main__':check()
