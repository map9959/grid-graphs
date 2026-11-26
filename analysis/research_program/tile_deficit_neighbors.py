"""Project a nine-tile window to its exact deficit-neighbor pattern."""
from itertools import product,combinations
from .defect_window import table,window
from .saturated_tile_phase import PHASE

def test():
    from pysat.solvers import Solver
    x=40;dom=set(product(range(31,52),repeat=2))
    def emit(f,bit,flags):
        tiles=[[bit(x+3*i+a,x+3*j+b) for a,b in product(range(3),repeat=2)] for i,j in product((-1,0,1),repeat=2)]
        small=[]
        for vs in tiles:
            z=f.nv+1;small.append(z)
            for ls in combinations(vs,3):f.append([-z,*[-t for t in ls]])
            for ls in combinations(vs,7):f.append([z,*ls])
        f.append([small[4]])
        rows=set()
        with Solver(name='cadical195',bootstrap_with=f.clauses) as s:
            while s.solve():
                m=set(s.get_model());v=sum((z in m)<<k for k,z in enumerate(small));rows.add(v)
                s.add_clause([-z if z in m else z for z in small])
        print('center deficient; feasible 3x3 deficit words',len(rows),'minimum other deficient tiles',min(v.bit_count()-1 for v in rows))
        print('minimal neighbor patterns',[format(v,'09b') for v in sorted(rows) if not any(w!=v and w&v==w for w in rows)])
        return rows
    return window(119,'rim',1,table(119),want=False,domain=dom,emit=emit,turn_domain=set())
if __name__=='__main__':test()
