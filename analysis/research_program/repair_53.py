"""Replay the upper-left cap change at 53 and its length-adjusted variants."""
from .zipper_rails import build,verify
from pathlib import Path


def parameters(n):
    base={47%42:47,53%42:53,71%42:71}[n%42]
    assert n>=base and (n-base)%42==0
    return {47:2,53:0,71:1}[base],(12 if base==71 else 9)+6*((n-base)//42)


def repaired(n):
    extra,m=parameters(n)
    rows=list(map(list,build(n,extra=extra)))
    rows[0][1]='.';rows[1][0]='#'
    for a in range(m//3+1):
        rows[a+2][3*a]='#'
        if 3*a<m:rows[a+2][3*a+2]='.'
    return list(map(''.join,rows))


if __name__=='__main__':
    assert repaired(53)==Path(__file__).with_name('forest_53_cap.txt').read_text().splitlines()
    for n in (53,95,137,179):
        s,e,c,t,f=verify(repaired(n));k=(n-2)//3
        upper=3*k*k+7*k+(23-2*k)//14
        assert s==f==upper
        print(n,'selected',s,'acyclic forced edges',e,'components',c,'tree edges',t,'full degree',f,'upper floor',upper)
