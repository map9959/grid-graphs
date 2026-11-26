"""Independent enumeration of source masks accepted by the two-board encoding."""
from .integral_rank_floor import Floor
from .integral_floor_cross import add_cross
from .skeleton_cross_rank import physical,verify
from pysat.solvers import Solver

if __name__=='__main__':
    expected=set()
    for mask in range(1<<16):
        rows=[''.join('#' if mask>>(4*i+j)&1 else '.' for j in range(4)) for i in range(4)]
        if '#..#' in rows or tuple('#..#') in zip(*rows):continue
        try:verify(rows)
        except AssertionError:continue
        _,j,A,X=physical(rows)
        if (j,A,X)==(0,1,0):expected.add(mask)
    model=Floor(4,0);add_cross(model,1,2);vs=sum(model.X,[]);got=set()
    with Solver(name='cadical195',bootstrap_with=model.f.clauses) as solver:
        while solver.solve():
            v=set(solver.get_model());got.add(sum((x in v)<<i for i,x in enumerate(vs)))
            solver.add_clause([-x if x in v else x for x in vs])
    assert got==expected
    print('all 65536 masks: paired model and physical floor enumeration agree on',len(got))
