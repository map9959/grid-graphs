"""Replay the side14 tile of the mixed-front negative-cycle family.

Only L=1 is materialized (n=14); larger members are a symbolic paper construction.
"""

import argparse
import json
from pathlib import Path

from analysis.interface_fillings.separation_audit import components
from .guarded_fronts import grid_edges, ledger, rows


WORD = [1,4,4,5,4,4,0,6,0]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    n, a, start = 14, 13, 2
    levels = [2,5,8,11]
    state = [False]*196
    for y in range(n):
        state[y*n] = True
    for y in levels:
        for x in range(2,a-2):
            state[y*n+x] = True
    for dy, mask in enumerate(WORD+[1]):
        for col in range(3):
            state[(start+dy)*n+a-2+col] = bool(mask & (1<<col))
    edges = grid_edges(n)
    info = ledger(state,n,edges)
    assert info == {"f":60,"r":7,"b":34,"c":31,"z":30}
    # No preserved singleton can pay the missing supplier-bank unit.
    neighbors = [[] for _ in state]
    for v,w in edges:
        neighbors[v].append(w)
        neighbors[w].append(v)
    singletons = [v for v,f in enumerate(state) if f and all(not state[w] for w in neighbors[v])]
    assert not singletons
    roots, _, forest = components(state, [(v,w) for v,w in edges if v%n<=a-3 and w%n<=a-3])
    assert forest and len({roots[y*n+a-3] for y in levels}) == 1
    off = [y for y in range(levels[0]+1,levels[-1]) if y not in levels]
    isolated = lambda v: not state[v] and all(not state[w] for w in neighbors[v])
    deep = [y*n+a-2 for y in off if isolated(y*n+a-2)]
    near = [y*n+a-1 for y in off if isolated(y*n+a-1)]
    holes_span = [y*n+a for y in range(2,12) if not state[y*n+a]]
    holes_window = [y*n+a for y in range(1,13) if not state[y*n+a]]
    pure_runs = []
    for y in range(n):
        if state[y*n+a] and (y==0 or not state[(y-1)*n+a]):
            run = []
            z = y
            while z<n and state[z*n+a]:
                run.append(z*n+a)
                z += 1
            if all(not state[v-1] for v in run):
                pure_runs.append(run)
    assert len(deep)==1 and not near and len(holes_span)==4 and len(holes_window)==6 and len(pure_runs)==1
    right = [a-3+int(mask & 1 != 0) for mask in [1,5,0,1]]
    actual_x = sum(min(r,s)-2 for r,s in zip(right,right[1:]))
    assert actual_x == 25
    dimer = [9*n+a-1,9*n+a]
    assert all(state[v] for v in dimer)
    assert all(not state[w] for v in dimer for w in neighbors[v] if w not in dimer)
    result = {"scope": "literal side14 realization only; all-size formulas require the accompanying paper proof",
              "rows":rows(state,n),"ledger":info,"rooted_back_cut":a-3,
              "marked_levels":levels,"word":WORD,"singleton_carriers":singletons,
              "deep_isolates":deep,"near_isolates":near,"span_holes":holes_span,
              "window_holes":holes_window,"pure_boundary_runs":pure_runs,
              "supplier_dimer":dimer,"actual_main_bank_straight_cells":actual_x,
              "symbolic_family": {"n":"9L+5","A":"9L+4","f":"27L^2+27L+6",
                 "r":"5L+2","b":"21L+13","c":"19L+12","K":"45L+27",
                 "r1":"0","X_main":"L(3A-14)","window_invoice":"5L+3",
                 "actual_demand_minus_invoice":"L-3-42L/A"}}
    with args.output.open("x") as out:
        json.dump(result,out,indent=2)
        out.write("\n")
    print("negative-cycle tile verified:",info,"main X",actual_x,"supplier dimer",dimer)


if __name__ == "__main__":
    main()
