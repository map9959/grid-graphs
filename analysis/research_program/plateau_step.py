"""Local growth of a north-rooted 7 plateau. Coordinates x,y are tile columns,rows."""
from .ordered_seam_price import table,rowchart
from .ordered_ports import typ
from pysat.formula import CNF,IDPool
from pysat.solvers import Solver

def box(axis,w,h,xs,ys,bad,*,alphabet=None):
    f=CNF();pool=IDPool()
    def bit(x,y):return pool.id(('m',x,y))
    def tile(x,y,m):return pool.id(('t',x,y,m))
    def color(x,y,b):return pool.id(('c',x,y,b))
    masks=[[set() for j in range(h)] for i in range(w)]
    for x in range(w-1):
        for y in range(h-1):
            ok=[]
            for (a,c),ls in table(axis,xs[x],ys[y],-4).items():
                for b,d in ls:
                    if y==0 and (a!=7 or c!=7):continue
                    if alphabet is not None and any(m not in alphabet for m in (a,b,c,d)):continue
                    z=pool.id(('tuple',x,y,a,b,c,d));ok.append(z)
                    for i,j,m in ((x,y,a),(x,y+1,b),(x+1,y,c),(x+1,y+1,d)):
                        masks[i][j].add(m);f.append([-z,tile(i,j,m)])
            f.append(ok)
    for x in range(w):
        for y in range(h):
            for m in masks[x][y]:
                v=tile(x,y,m)
                for a in range(3):
                    for b in range(3):
                        z=bit(3*x+a,3*y+b);f.append([-v,z if m>>(3*a+b)&1 else -z])
    f.append([bit(3*x+a,3*y+b) if not(7>>(3*a+b)&1) else -bit(3*x+a,3*y+b)
              for x,y in bad for a in range(3) for b in range(3)])
    H=3*h;W=3*w
    # Known teeth from the north trunks, the actual east/south teeth
    # (when present), all have distinct components. Empty-edge components
    # can leave the box; no guessed donors or extra boundary conditions.
    roots=[(3*x,1) for x in range(w)]
    if xs[-1]==37:roots.extend((W-2,y) for y in range(H))
    if ys[-1]==37:roots.extend((x,H-2) for x in range(W))
    roots=list(dict.fromkeys(roots));B=len(roots).bit_length()
    for code,(x,y) in enumerate(roots):
        for b in range(B):f.append([-bit(x,y),color(x,y,b)*(1 if code>>b&1 else -1)])
    for x in range(W):
        for y in range(H):
            for u,v in ((x+1,y),(x,y+1)):
                if u>=W or v>=H:continue
                for b in range(B):
                    a=color(x,y,b);c=color(u,v,b)
                    for m in (bit(x,y),bit(u,v)):f.extend([[-m,-a,c],[-m,a,-c]])
    return f,bit

def pilot(a,w,h,extra=0):
    f,bit=box(a,w,h,[7]*(w-1),[7]*(h-1),[(3,y) for y in range(1,5)])
    with Solver(name='cadical195',bootstrap_with=f.clauses) as s:
        yes=s.solve();print(a,w,h,'SAT',yes)
        if yes:
            m=set(s.get_model())
            for y in range(h):
                print([sum(1<<(3*b+c) for b in range(3) for c in range(3) if bit(3*x+b,3*y+c) in m) for x in range(w)])
if __name__=='__main__':
    import sys
    pilot(*map(int,sys.argv[1:]))
