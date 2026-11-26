"""Test corner extensions against the all-size bulk axis dichotomy."""
from itertools import product
from .defect_window import table,window
from .slit_star_transfer import frame_path

def test(n,width):
    from pysat.solvers import Solver
    tab=table(n);frames=[frame_path(n,w) for w in range(16)]
    ok={(w,o) for w in range(16) for o in range(2)}
    for a,b in product(range(2),repeat=2):
        ax=lambda h:range(n-width,n) if h else range(width)
        dom=set(product(ax(a),ax(b)))
        def emit(f,bit,flags,arc,sheet):
            tests={}
            for w,(m,p) in enumerate(frames):
                literals=[bit(*u)*(1 if v else -1) for u,v in sorted(m.items()) if u in dom]
                literals.extend(arc(*u,d)*(1 if d==v else -1) for u,v in sorted(p.items()) if u in dom
                                for d,(dr,dc) in enumerate(((0,1),(1,0),(0,-1),(-1,0))) if (u[0]+dr,u[1]+dc) in dom)
                tests.setdefault(tuple(literals),[]).append(w)
            for o in range(2):
                with Solver(name='cadical195',bootstrap_with=f.clauses) as s:
                    for i,j in dom:
                        if min(i,j,n-1-i,n-1-j)<14 or i%3!=2 or j%3!=2:continue
                        for h in (-1,1):
                            v=i+h*(o==0),j+h*(o==1)
                            if v in dom:s.add_clause([-bit(i,j),-bit(*v)])
                    for lits,ws in tests.items():
                        if not s.solve(assumptions=lits):ok.difference_update((w,o) for w in ws)
            print('corner',a,b,'survivors',len(ok),flush=True)
        window(n,'rim',1,tab,want=False,root_site=(n-1,n-1),domain=dom,emit_graph=emit)
    print('far-star corner relaxation, surviving (frame,forbidden axis)',sorted(ok))
if __name__=='__main__':
    import sys
    test(*map(int,sys.argv[1:]))
