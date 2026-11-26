"""Route a marked cap tip to the merger, and test covering neutral alternatives."""
from itertools import product
from collections import Counter
from .double_rail_window import run
from .zipper_rails import build
from .rail_swap_uniform import geometry,expr
from .run_rail_swap import DIR

caprm={(1,2),(3,1)}
capins={(2,0),(2,1),(2,2)}
cut=(2,2)
rect=([(2,j) for j in range(-6,5)]+[(i,4) for i in range(3,6)]+
      [(5,j) for j in range(3,-7,-1)]+[(i,-6) for i in (4,3)])
def shift(u,v):return u[0]+v[0],u[1]+v[1]
def edges(path):return zip(path,path[1:]+path[:1])

def replay(n):
    t=(n-35)//42;u=(8+7*t,17+21*t);v=(29+42*t,6+6*t)
    X={(i,j) for i,row in enumerate(build(n)) for j,b in enumerate(row) if b=='#'}
    X.difference_update(shift(v,p) for p in caprm);X.update(shift(v,p) for p in capins)
    X.remove(shift(v,cut));X.add(u)
    board=set(product(range(n),repeat=2))
    lost={p for p in board-X if not any(shift(p,d) in X for d in DIR)}
    assert lost=={shift(v,(1,2)),shift(v,(3,2))}
    todo=[(0,0)];seen=set(todo)
    for p in todo:
        for d in DIR:
            q=shift(p,d)
            if q in board and q not in seen and (p in X or q in X):
                seen.add(q);todo.append(q)
    assert seen==board-lost
    E=sum(shift(p,d) in board and (p in X or shift(p,d) in X) for p in board for d in DIR[:2])
    r=len(X)-sum(shift(p,d) in X for p in X for d in DIR[:2])
    assert E-len(seen)+1==2 and r==8*n//7-2
    print(n,'marks',len(X),'runs',r,'uncovered',sorted(lost),'nontrivial components 1; cycle rank 2')

def uniform():
    inside,marks=geometry()
    C=expr('t>=2 and i=29+42t and j=6+6t');U=expr('t>=2 and i=8+7t and j=17+21t')
    def in_cap(p):
        if p in caprm or p==cut:return False
        if p in capins:return True
        assert (C-marks(p)).none() or (C&marks(p)).none()
        return (C-marks(p)).none()
    def in_merger(p):
        if p==(0,0):return True
        assert (U-marks(p)).none() or (U&marks(p)).none()
        return (U-marks(p)).none()
    assert not in_cap((2,2)) and not in_cap((2,3))
    for p in ((1,2),(3,2)):
        assert not any(in_cap(shift(p,d)) for d in ((0,0),*DIR))
    for side in (-1,1):
        cycle=[(0,0),(0,side),(0,2*side),(1,2*side),(2,2*side),(2,side),(2,0),(1,0)]
        assert all(in_merger(a) or in_merger(b) for a,b in edges(cycle))
    # The old top tooth is continuous from row two to the row above
    # the added site; the old right rail continues down to the bottom teeth.
    assert (expr('t>=2 and j=17+21t and 2<=i<=7+7t')-marks((0,0))).none()
    assert (expr('t>=2 and j=19+21t and 8+7t<=i<=32+42t')-marks((0,0))).none()
    assert (expr('t>=2 and i=0 and j=17+21t')-marks((0,0))).none()
    assert (expr('t>=2 and i=34+42t and j=19+21t')-marks((0,0))).none()
    print('all t>=2: cap cycle cut and top/bottom joined; two uncovered cap sites and two forced 8-cycles')
    # Start again from the seven-mark cap. A one-mark relocation must
    # delete a unique marked endpoint of an edge of the 26-cycle.
    occupied=lambda p:p==cut or in_cap(p)
    cl=lambda u:{u}|{shift(u,d) for d in DIR}
    cutters={p for p,q in edges(rect) if occupied(p) and not occupied(q)}
    cutters.update(q for p,q in edges(rect) if occupied(q) and not occupied(p))
    cutters={p for p in cutters if (C-inside(p)).none()}
    for x in cutters:
        lost=[v for v in cl(x) if all(not occupied(p) for p in cl(v)-{x})]
        assert lost
        options=set.intersection(*(cl(v) for v in lost))
        for z in options:
            if occupied(z) or not (C-inside(z)).none():continue
            if any(shift(z,d)!=x and occupied(shift(z,d)) for d in ((1,1),(1,-1),(-1,1),(-1,-1))):continue
            old=sum(occupied(shift(x,d)) for d in DIR)
            new=sum(shift(z,d)!=x and occupied(shift(z,d)) for d in DIR)
            assert old!=new
    print('all t>=2:',len(cutters),'interior one-mark cycle cutters; no covering single relocation anywhere preserves the run count')

def windows(n):
    # The base two-window halos have already been proved invariant as
    # integer sets; the edited cap differs only at the five fixed offsets.
    A=run(n,'cap',True,True);B=run(n,'merger',True,True)
    _,_,_,_,X,_,_=run(n,'cap',False,True)
    count=Counter()
    for (r,i,e),opts in A.items():
        if not r:continue
        for rm,ins in opts:
            Y=(X-set(rm))|set(ins)
            if all(a in Y or b in Y for a,b in edges(rect)):continue
            for k in (1,2):
                if i>=k or r>k:continue
                count[k]+=len(B.get((k-r,k-i,-e),[]))
    print(n,'covering neutral edits cutting the cap cycle with a merger insertion:',
          {k:count[k] for k in (1,2)})
    return count
if __name__=='__main__':
    uniform()
    for n in (119,161,203):
        replay(n);assert not any(windows(n).values())
