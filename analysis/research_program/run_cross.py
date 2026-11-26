"""Orientation-split run ledger on perpendicular bands. Costs are doubled."""
from itertools import product
from pysat.formula import CNF,IDPool
from pysat.pb import PBEnc
from pysat.solvers import Solver

def instance(n,cy,cx,h,cost):
    P=IDPool();f=CNF();weights={}
    def bit(i,j):return P.id(('m',i,j))
    D={(i,j) for i,j in product(range(n),repeat=2) if cy-1<=i<=cy+h or cx-1<=j<=cx+h}
    def bill(reason,c):
        u=P.id();f.append([*reason,u]);weights[u]=c
    dirs=((0,1),(1,0),(0,-1),(-1,0))
    for i,j in D:
        m=bit(i,j);horiz=P.id(('h',i,j))
        vs=[];arcs=[]
        for s,(di,dj) in enumerate(dirs):
            u,v=i+di,j+dj
            if (u,v) not in D:continue
            a=bit(u,v);vs.append(a)
            f.append([-m,-a,horiz if di==0 else -horiz])
            arc=P.id(('a',i,j,s));arcs.append(arc)
            if s<2:
                rev=P.id(('a',u,v,s+2))
                f.extend([[-arc,-rev],[-m,arc,rev],[-a,arc,rev],[-arc,m,a],[-rev,m,a]])
            for l,(du,dv) in enumerate(dirs):
                if (u+du,v+dv) not in D or (l-s)%4==2:continue
                nxt=P.id(('a',u,v,l));p=P.id(('s',i,j));q=P.id(('s',u,v))
                if abs(s-l)==3:q=-q
                f.extend([[-arc,-nxt,-p,q],[-arc,-nxt,p,-q]])
        for z,arc in enumerate(arcs):
            for b in arcs[:z]:f.append([-arc,-b])
        V=cx<=j<cx+h;H=cy<=i<cy+h
        if V:bill([-m,horiz,*([bit(i-1,j)] if i else [])],2)
        if H:bill([-m,-horiz,*([bit(i,j-1)] if j else [])],2)
        if V or H:bill([m,*vs],int(V)+int(H))
        if V and i in (0,n-1):bill([m],2)
        if H and j in (0,n-1):bill([m],2)
    f.extend(PBEnc.atmost(lits=list(weights),weights=list(weights.values()),bound=cost,vpool=P,encoding=8).clauses)
    return f,D,bit

def pilot(n,cy,cx,h,c):
    f,D,bit=instance(n,cy,cx,h,c)
    with Solver(name='cadical195',bootstrap_with=f.clauses) as s:
        s.conf_budget(30000);v=s.solve_limited();print(n,cy,cx,h,c,'SAT',v,flush=True)
        if v:
            m=set(s.get_model());print('\\n'.join(''.join('#' if bit(i,j) in m else '.' for j in range(n)) for i in range(cy,cy+h)))
if __name__=='__main__':
    import sys
    pilot(*map(int,sys.argv[1:]))
