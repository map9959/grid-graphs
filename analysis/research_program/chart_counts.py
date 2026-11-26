"""Symbolically count one diagonal-chart bucket at sizes S+6t, t>=0."""
from fractions import Fraction as Q
from itertools import product

def count(S,d,W,pos):
    def axis(k,z):
        if k<d:return ((k,0),(k,0)) if z==k%3 else None
        if k<d+3:return ((d,0),(S-1-d,6)) if z==k%3 else None
        a=k+S-2*d-3;return ((a,6),(a,6)) if z==a%3 else None
    def floor(A,b):a,s=A;assert s%b==0;return a//b,s//b
    def ceil(A,b):a,s=A;assert s%b==0;return -((-a)//b),s//b
    def maxlin(v):
        a,b=max(v,key=lambda z:(z[1],z[0]));assert all(a>=x for x,y in v),(S,pos,v)
        return a,b
    def minlin(v):a,b=maxlin([(-a,-b) for a,b in v]);return -a,-b
    total=[0,0,0]
    for r,c in product(range(3),repeat=2):
        ra=axis(pos[0],r);ca=axis(pos[1],c)
        if not ra or not ca:continue
        X=(ceil((ra[0][0]-r,ra[0][1]),3),floor((ra[1][0]-r,ra[1][1]),3))
        # y >= or <= slope*x + A+B*t, where i=3x+r and j=3y+c.
        low=[(0,*ceil((ca[0][0]-c,ca[0][1]),3))];hi=[(0,*floor((ca[1][0]-c,ca[1][1]),3))]
        u,v=pos[2:]
        if u<W:low.append((1,*ceil((r-c-u,0),3)))
        if u>-W:hi.append((1,*floor((r-c-u,0),3)))
        if v>-W:low.append((-1,*ceil((S-1+v-r-c,6),3)))
        if v<W:hi.append((-1,*floor((S-1+v-r-c,6),3)))
        for i,L in enumerate(low):
            for j,U in enumerate(hi):
                left=[X[0]];right=[X[1]];const=[]
                def ge(a,b,strict):
                    s,A,B=(x-y for x,y in zip(a,b));A-=strict
                    if s>0:left.append(ceil((-A,-B),s))
                    elif s<0:right.append(floor((A,B),-s))
                    else:const.append((A,B))
                # Break all ties by least line index.
                for z,a in enumerate(low):ge(L,a,z<i)
                for z,a in enumerate(hi):ge(a,U,z<j)
                ge(U,L,False)
                if any(a<0 and b<=0 for a,b in const):continue
                if any(a<0 or b<0 for a,b in const):
                    # A parallel pair changes order only outside a sufficiently
                    # large base chart. Do not extrapolate such a piece.
                    raise AssertionError(('crossing parallel lines',pos,S,const))
                a,b=maxlin(left);c0,e=minlin(right)
                if c0<a and e<=b:continue
                assert c0>=a and e>=b
                for t in range(3):
                    x=a+b*t;y=c0+e*t
                    z=Q((y-x+1)*((U[0]-L[0])*(x+y)+2*(U[1]-L[1]+(U[2]-L[2])*t+1)),2)
                    assert z.denominator==1;total[t]+=int(z)
    a,b,c=total;return a,b-a,c-2*b+a
