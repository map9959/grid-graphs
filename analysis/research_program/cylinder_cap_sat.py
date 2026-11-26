"""All-height cap search at a fixed tangential period; event budget is independent of H."""
from pysat.card import CardEnc
from pysat.formula import CNF,IDPool
from .sector_gap_cover import verify
from pysat.solvers import Solver

def model(w,h,gain,reduced=False):
    P=IDPool();f=CNF();cost=[];ds=((0,1),(1,0),(0,-1),(-1,0))
    def mark(y,x):return P.id(('m',y,x%w))
    def arc(y,x,s):return P.id(('a',y,x%w,s))
    prefix=None
    for y in range(h):
        if reduced:
            rail=[mark(y,x)*(1 if x%3==0 else -1) for x in range(w)]
            a=P.id()
            for lit in rail:f.append([-a,lit])
            f.append([a,*[-v for v in rail]])
            if y:
                for ph in range(3):
                    diff=[mark(j,x)*(-1 if x%3==ph else 1) for j in (y-1,y) for x in range(w)]
                    f.append(diff+([prefix] if ph==0 else []))
                new=P.id();f.extend([[-new,prefix],[-new,a],[new,-prefix,-a]]);a=new
            prefix=a
            if y<h-1:f.append([-mark(y,x) for x in range(w)])
        for x in range(w):
            m=mark(y,x);arcs=[]
            if not y:
                if x%3:f.append([-m])
            if y==h-1:cost.append(-m)
            if y:
                start=P.id();f.append([-m,mark(y,x-1),mark(y-1,x),start]);cost.append(start)
            for s,(dy,dx) in enumerate(ds):
                j=y+dy;i=(x+dx)%w
                if j==-1 and x%3==0:
                    a=arc(y,x,s);arcs.append(a);f.append([a]);continue
                if not 0<=j<h:continue
                a=arc(y,x,s);arcs.append(a)
                if s<2:
                    mm=mark(j,i);b=arc(j,i,s+2)
                    f.extend([[-m,a,b],[-mm,a,b],[-a,-b],[-a,m,mm],[-b,m,mm]])
                for l,(ey,ex) in enumerate(ds):
                    if l==(s+2)%4 or not 0<=j+ey<h:continue
                    b=arc(j,i,l);z=P.id(('sheet',y,x));v=P.id(('sheet',j,i))
                    if abs(s-l)==3:v=-v
                    f.extend([[-a,-b,-z,v],[-a,-b,z,-v]])
            for idx,a in enumerate(arcs):
                for b in arcs[:idx]:f.append([-a,-b])
            sink=P.id();f.append([*arcs,sink]);cost.append(sink)
            if reduced:
                if y or x%3:
                    f.append([sink,m,*[mark(y+i,x+j) for i,j in ds if 0<=y+i<h]])
                for b in range((w//3).bit_length()):
                    c=P.id(('root',y,x,b))
                    if not y and x%3==0:f.append([c*(1 if (x//3)>>b&1 else -1)])
                    for dy,dx in ds[:2]:
                        if y+dy==h:continue
                        d=P.id(('root',y+dy,(x+dx)%w,b))
                        for v in (m,mark(y+dy,x+dx)):f.extend([[-v,-c,d],[-v,c,-d]])
            if y:
                for dx in (-1,1):f.append([-m,-mark(y-1,x+dx)])
    f.extend(CardEnc.atmost(cost,2*(w//3)-3*gain,vpool=P).clauses)
    return f,mark

def run(w,h,gain,cert=False,reduced=False):
    f,mark=model(w,h,gain,reduced)
    with Solver(name='cadical195',bootstrap_with=f.clauses) as s:
        s.conf_budget(50000);yes=s.solve_limited();print(w,h,gain,yes,flush=True)
        if yes:
            m=set(s.get_model());rows=[''.join('#' if mark(y,x) in m else '.' for x in range(w)) for y in range(h)]
            assert sum(r.count('#') for r in rows)>=h*(w//3)+gain
            print(*rows,sep='\n');return rows
    if yes is False and cert:assert verify(f,f'cylinder{w}_{h}_{gain}')
if __name__=='__main__':
    import sys
    run(*map(int,sys.argv[1:4]),cert='--drat' in sys.argv,reduced='--reduced' in sys.argv)
