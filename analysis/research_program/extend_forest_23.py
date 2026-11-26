"""Try all three-row/three-column insertion seams, then an unrestricted search."""
from pathlib import Path
from .extend_forest_28 import verify


def old(n=23):
    return Path(__file__).with_name(f'forest_{n}.txt').read_text().splitlines()


def image(rows,i,j):
    return {(r+3*(r>=i),c+3*(c>=j)) for r,s in enumerate(rows) for c,x in enumerate(s) if x=='#'}


def search(n=26):
    from .side28_sat import cnf,cycle
    from pysat.solvers import Solver
    f,sites=cnf(n);r=old(n-3)
    cuts=sorted(((i,j) for i in range(n-2) for j in range(n-2)),
                key=lambda ij:abs(ij[0]-8)+abs(ij[1]-1))
    with Solver(name='cadical195',bootstrap_with=f) as s:
        for i,j in cuts+[(None,None)]:
            if i is None:print(f'no mark-preserving solution on {len(cuts)} seam pairs; trying unrestricted',flush=True)
            a=[sites[n*u+v] for u,v in image(r,i,j)] if i is not None else []
            while s.solve(assumptions=a):
                sol=set(s.get_model());v={u for u,x in enumerate(sites) if x in sol}
                p=cycle(v,n)
                if p:
                    s.add_clause([-sites[u] for u in p if u in v]);continue
                rows=[''.join('#' if n*u+w in v else '.' for w in range(n)) for u in range(n)]
                assert verify(rows)[0]=={26:248,29:306,32:370,35:440,38:515,41:597}[n]
                print('seams',i,j,'forest',verify(rows),flush=True)
                Path(__file__).with_name(f'forest_{n}.txt').write_text('\n'.join(rows)+'\n')
                return
        print('no witness found')


def replay(n=26):
    rows=old(n)
    assert len(rows)==n and all(len(r)==n and set(r)<={'.','#'} for r in rows)
    s,e,c,t,f=verify(rows)
    assert s==f=={26:248,29:306,32:370,35:439,38:515,41:597}[n]
    print(f'side {n}: selected',s,'acyclic forced edges',e,'components',c,'tree edges',t,'full-degree vertices',f)
    base=old(n-3)
    seams=[(i,j) for i in range(n-2) for j in range(n-2) if all(rows[u][v]=='#' for u,v in image(base,i,j))]
    print(f'seams retaining all {sum(r.count("#") for r in base)} old marks:',seams)


if __name__=='__main__':
    import sys
    n=41 if '--41' in sys.argv else 38 if '--38' in sys.argv else 35 if '--35' in sys.argv else 32 if '--32' in sys.argv else 29 if '--29' in sys.argv else 26
    if '--search' in sys.argv:search(n)
    else:replay(n)
