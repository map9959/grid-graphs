"""Cycle3 refinement: complete arbitrary two-column exteriors of stopped fronts.

python3 -m analysis.research_program.stopped_fronts OUTPUT.json
"""

import argparse
import json
from pathlib import Path

from analysis.interface_fillings.separation_audit import components
from .guarded_fronts import grid_edges, rows


def fixture(n, levels, first_free, last_free):
    a = n-1
    state = [False] * (n*n)
    for y in levels:
        for x in range(a-2):
            state[y*n+x] = True
    optional = [y*n+x for y in range(first_free, last_free+1) for x in (a-1,a)]
    return state, optional


def run(n, levels, first_free, last_free):
    assert 8 <= n <= 15
    base, optional = fixture(n, levels, first_free, last_free)
    assert len(optional) <= 20
    edges = grid_edges(n)
    a = len(levels)-1
    offlevels = [y for y in range(levels[0]+1, levels[-1]) if y not in levels]
    assert len(offlevels) == 2*a
    masks = []
    invoices = {}
    corner_hole_cases = 0
    examples = {}
    for mask in range(1 << len(optional)):
        state = base.copy()
        for i, v in enumerate(optional):
            state[v] = bool(mask & (1 << i))
        roots, _, forest = components(state, edges)
        if not forest:
            continue
        masks.append(mask)
        z, h = [], []
        for y in offlevels:
            u, s, boundary = y*n+n-3, y*n+n-2, (y+1)*n+n-1
            assert not state[u]
            if state[s]:
                assert not state[boundary]
                h.append(boundary)
            else:
                assert all(not state[w if v == u else v] for v, w in edges if u in (v,w))
                z.append(u)
        assert len(z)+len(h) == 2*a and len(set(z)) == len(z) and len(set(h)) == len(h)
        # The specified actual bank has a+1 full rails, q=1, W=n-4.
        demand_numerator = max(0, 3*a*(n-4)-a*(n-1))
        assert demand_numerator <= (n-1)*(len(z)+len(h))
        key = f"z{len(z)}_h{len(h)}"
        invoices[key] = invoices.get(key, 0)+1
        if key not in examples:
            examples[key] = {"mask": mask, "isolates": z, "right_side_hole_units": h,
                             "rail_root_count": len({roots[y*n+n-4] for y in levels})}
        if n*n-1 in h:
            corner_hole_cases += 1
    print(f"stopped{n}: {1 << len(optional)} masks, {len(masks)} feasible, invoices {invoices}, corner-hole cases {corner_hole_cases}")
    return {"n": n, "levels": levels, "base_rows": rows(base,n), "optional": optional,
            "first_free": first_free, "last_free": last_free,
            "subsets": 1 << len(optional), "feasible_masks": masks,
            "demand_numerator": max(0,3*a*(n-4)-a*(n-1)), "demand_denominator": n-1,
            "invoice_histogram": invoices, "examples": examples, "corner_hole_cases": corner_hole_cases}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    with args.output.open("x") as output:
        fixtures = [run(11,[2,5,8],1,9), run(14,[4,7,10,13],4,13)]
        json.dump({"schema": 1, "scope": "complete specified two-column exteriors; no spine/root assumption; original-resource invoices",
                   "fixtures": fixtures}, output, indent=2)
        output.write("\n")


if __name__ == "__main__":
    main()
