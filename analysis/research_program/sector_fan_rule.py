"""Price-free side collar: a four-step spacing seeds two five-step fronts."""
from itertools import product
from .sector_gap_cover import verify
from .diagonal_score import data,generate
from pysat.solvers import Solver

def birth(x,y):
    if y==0:return True
    if y==1:return False
    a=-3*(y-2);b=4+3*(y-2)
    return x<=a and (x-a)%3==0 or x>=b and (x-b)%3==0 or a+5<=x<=b-5 and (x-a-5)%3==0

def right(x,l):return x<=l and (x-l)%3==0 or x>=l+5 and (x-l-5)%3==0

def check(n,t,tables,I,J,units,output,tag):
    f,X=generate(n,t,set(product(I,J)),True,tables)
    lit=lambda i,j,b:X[i*n+j]*(1 if b else -1)
    for i,j,b in units:f.append([lit(i,j,b)])
    with Solver(name='cadical195',bootstrap_with=f.clauses) as s:assert s.solve(),tag
    f.append([-lit(i,j,b) for i,j,b in output])
    assert verify(f,tag)

def run(n):
    k=n//3;t=3*k*k+(32*k-7)//6;tabs=data(n,t)
    for a in range(3):
        x=60+a
        check(n,t,tabs,range(12),range(x-20,x+23),[(2,x,1),(2,x+4,1)],
              [(y,x+z,birth(z,y)) for y,z in product(range(7),range(-14,19))],f'birth{n}_{a}')
        for b in range(3):
            y=24+b
            check(n,t,tabs,range(y-4,y+12),range(x-14,x+20),
                  [(y-i,x+j,right(j,-3*i)) for i,j in product(range(2),range(-12,18))],
                  [(y+1,x+j,right(j,3)) for j in range(-3,12)],f'right{n}_{a}{b}')
if __name__=='__main__':
    for n in (199,208):run(n)
