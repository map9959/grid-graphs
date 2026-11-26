"""Test the solved-neighbor comparison on full-bar caps with explicit strip words."""
from fractions import Fraction as Q
from .comb_cap_transfer import construct
from .extend_forest_28 import verify
from .wired_strip_flow import advance

MOTIF={5:((15,0,2,10),(8,9,8,10)),7:((47,32,36),(33,40,34,34,42,34,34,40,33,36,36,37,36,36))}

def strip(h,n):
    prefix,word=MOTIF[h]
    state=(0,-1,tuple(range(h)))
    def read(st,m):
        z=advance(h-1,st,m,False)
        assert z is not None
        return 0,z[1],z[2]
    for m in prefix:state=read(state,m)
    start=state
    for m in word:state=read(state,m)
    assert state==start
    return (prefix+word*(1+n//len(word)))[:n]

def embed(n,h):
    rows=construct(n,4);r=rows[3]
    assert r==rows[4] and r=='#..'*(n//3)+'#'
    rows=rows[:4]+[r]*h+rows[4:]
    width=n+h;word=strip(h,width)
    extended=[s+'.'+''.join('#' if m>>j&1 else '.' for j in range(h-1)) for s,m in zip(rows,word)]
    tree=verify(extended)
    count=sum(s.count('#') for s in rows)+sum(m.bit_count() for m in word)
    assert tree[0]==count
    upper=3*(width//3)**2+(3*(width//3)-2 if width%3==0 else
                7*(width//3)-(width//3-5)//7-int(width//3%14==11))
    assert count<=upper
    print(n,'+',h,'score',count,'neighbor upper',upper,'physical tree',tree)

if __name__=='__main__':
    for h in MOTIF:
        w=MOTIF[h][1];print('full-bar depth',h,'achieved deficit',Q(h,3)-Q(sum(m.bit_count() for m in w),len(w)))
        embed(103,h)
