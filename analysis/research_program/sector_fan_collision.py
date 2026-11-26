"""Finite recurrence excluding two inward five-spacings in clean flat sectors."""
from .sector_fan_rule import check,right,product,data,generate,verify
from pysat.solvers import Solver

def pair(x,y,g):
    l=3*y;r=g-3*y
    return (x<=l and (x-l)%3==0 or x>=r and (x-r)%3==0 or
            l+5<=x<=r-5 and (x-l-5)%3==0)

def audit(n):
    k=n//3;t=3*k*k+(32*k-7)//6;tables=data(n,t)
    for a,b in product(range(3),repeat=2):
        x=69+a;y=24+b;I=range(y-4,y+12)
        check(n,t,tables,I,range(x-14,x+20),[(y+i,x+j,right(j,3*i))
              for i,j in product((-1,0),range(-6,12))],
              [(y+1,x+j,right(j,3)) for j in range(-3,9)],f'lip{n}_{a}{b}')
        # All three stripe phases in one disjoint selector test.
        f,X=generate(n,t,set(product(I,range(x-14,x+20))),True,tables)
        flags=[f.nv+i+1 for i in range(3)];f.append(flags)
        for p,z in enumerate(flags):
            for i,j in product((-1,0),range(-3,4)):
                f.append([-z,X[(y+i)*n+x+j]*(1 if j%3==p else -1)])
            f.append([-z,X[(y+1)*n+x]*(-1 if p==0 else 1)])
        assert verify(f,f'straight{n}_{a}{b}')
        for g in (16,19):
            f,X=generate(n,t,set(product(I,range(x-14,x+g+15))),True,tables)
            for i,j in product((-1,0),range(-6,g+7)):
                f.append([X[(y+i)*n+x+j]*(1 if pair(j,i,g) else -1)])
            assert verify(f,f'collision{n}_{a}{b}_{g}')

def location_check():
    for g in range(22,110,3):
        for i in (-1,0):
            assert all(pair(x,i,g)==right(x,3*i) for x in range(-6,12))
            assert all(pair(g-x,i,g)==right(x,3*i) for x in range(-6,12))
            for x in range(9,g-8):
                assert all(pair(z,i,g)==((z-5)%3==0) for z in range(x-3,x+4))
        for x in range(-3,g+4):
            assert pair(x,1,g)==(right(x,3) if x<=8 else right(g-x,3) if x>=g-8 else (x-5)%3==0)
if __name__=='__main__':
    location_check()
    for n in (199,208):audit(n)
