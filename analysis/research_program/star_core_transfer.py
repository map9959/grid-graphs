"""Find identical physical mark constraints in the trimmed 119 and 161 proofs."""
from pathlib import Path
from collections import Counter
import sys

def extract(n,H,side,rim,bit,arc,sheet):
    base=Path(f'target/star_rim_{n}_{H}_0_0_{side}_far_{side}')
    # Original window allocated all mark variables before this hook.
    inv={bit(*u):u for u in rim};clauses=set()
    for line in base.with_suffix('.core').open():
        if line.startswith('p'):continue
        lits=list(map(int,line.split()))[:-1]
        if lits and all(abs(x) in inv for x in lits):
            clauses.add(tuple(sorted((*inv[abs(x)],int(x>0)) for x in lits)))
    path=base.with_suffix('.marks')
    path.write_text(''.join(' '.join(str(z) for v in c for z in v)+'\n' for c in sorted(clauses)))
    print('side',n,side,'mark-only core clauses',len(clauses))

def compare(side):
    sets=[]
    for n in (119,161):
        path=Path(f'target/star_rim_{n}_8_0_0_{side}_far_{side}.marks')
        clauses=set()
        for line in path.open():
            a=iter(map(int,line.split()));clauses.add(tuple(zip(a,a,a)))
        sets.append(clauses)
    # Delete 42 consecutive rows and columns in the larger core.
    # The two-dimensional clauses must match literal-for-literal after deletion.
    best=None
    for cut in range(15,100,6):
        def axis(x):return x if x<cut else x-42 if x>=cut+42 else -1
        part=set()
        for c in sets[1]:
            z=tuple((axis(i),axis(j),b) for i,j,b in c)
            if all(min(i,j)>=0 for i,j,b in z) and z in sets[0]:part.add(z)
        if best is None or len(part)>best[0]:best=len(part),cut,part
    size,cut,part=best
    print(side,'common physical clauses',size,'best deletion cut',cut,
          'by arity',dict(sorted(Counter(map(len,part)).items())))
    from pysat.solvers import Solver
    cnf=[[(119*i+j+1)*(1 if b else -1) for i,j,b in c] for c in part]
    with Solver(name='cadical195',bootstrap_with=cnf) as solver:
        assert solver.solve()
        model=set(solver.get_model())
        assert all(any(v in model for v in c) for c in cnf)
    print('common mark clauses alone: SAT, assignment checked clause by clause')
    # A phase-respecting start for a 39-column replaceable segment,
    # chosen around that cut, avoiding corners in the smaller board.
    a=3*(min(63,max(12,cut-21))//3)
    print('test seam at',a)
if __name__=='__main__':compare(sys.argv[1])
