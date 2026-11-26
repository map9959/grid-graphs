"""Batch001: complete extension tests of guarded depth-three exchanges.

python3 -m analysis.research_program.guarded_fronts OUTPUT.json
"""

import argparse
import json
from pathlib import Path

from analysis.interface_fillings.separation_audit import components


def grid_edges(n):
    return [(y*n+x, yy*n+xx) for y in range(n) for x in range(n)
            for xx, yy in [(x+1, y), (x, y+1)] if xx < n and yy < n]


def rows(state, n):
    return ["".join("." if f else "U" for f in state[y*n:(y+1)*n]) for y in range(n)]


def ledger(state, n, edges):
    _, c, forest = components(state, edges)
    assert forest
    adjacency = [[] for _ in state]
    forced_degree = [0] * len(state)
    degree = [0] * len(state)
    for v, w in edges:
        degree[v] += 1
        degree[w] += 1
        if state[v] or state[w]:
            forced_degree[v] += 1
            forced_degree[w] += 1
        if state[v] and state[w]:
            adjacency[v].append(w)
            adjacency[w].append(v)
    seen = set()
    r = 0
    for v, is_f in enumerate(state):
        if not is_f or v in seen:
            continue
        r += 1
        seen.add(v)
        stack = [v]
        while stack:
            for w in adjacency[stack.pop()]:
                if w not in seen:
                    seen.add(w)
                    stack.append(w)
    result = {"f": sum(state), "r": r,
              "b": sum(4-degree[v] for v, f in enumerate(state) if not f),
              "c": c, "z": forced_degree.count(0)}
    assert 3*result["f"]+r+result["b"]+c == n*n+4*n
    return result


def rooted14():
    n = 14
    state = [False] * (n*n)
    for y in range(3, 11):
        state[y*n+3] = True
    for y in (4, 7, 10):
        for x in range(5, 11):
            state[y*n+x] = True
    for y in (0, 1):
        state[y*n+3] = True
    for x in range(5, 12):
        state[x] = True
    for y in range(11):
        state[y*n+13] = True
    return state


def rootless14():
    state = [False] * 196
    for y in (4, 7, 10):
        for x in range(11):
            state[y*14+x] = True
    for y in range(3, 12):
        state[y*14+13] = True
    return state


def rooted15():
    state = [False] * 225
    for y in range(15):
        state[y*15+1] = state[y*15+14] = True
    for y in (1, 4, 7, 10):
        for x in range(3, 12):
            state[y*15+x] = True
    for x in range(3, 13):
        state[14*15+x] = True
    return state


def exchange(state, n, selected):
    result = state.copy()
    for y in selected:
        d, p = y*n+n-1, y*n+n-3
        assert result[d] and not result[p]
        result[d], result[p] = False, True
    return result


def patch(n, x, y, w, h):
    return [yy*n+xx for yy in range(y, y+h) for xx in range(x, x+w)]


def run_fixture(name, n, base, levels, selected, region):
    assert 8 <= n <= 15
    edges = grid_edges(n)
    protected_u = [y*n+n-3 for y in levels]
    optional = [v for v in region if not base[v] and v not in protected_u]
    assert len(optional) <= 20
    base_ledger = ledger(base, n, edges)
    isolates = [(y+dy)*n+n-3 for y in selected for dy in (-1, 1)]
    feasible_masks = []
    deltas = {"f": 0, "r": len(selected), "b": len(selected),
              "c": -2*len(selected), "z": -2*len(selected)}
    for mask in range(1 << len(optional)):
        state = base.copy()
        for i, v in enumerate(optional):
            state[v] = bool(mask & (1 << i))
        _, _, forest = components(state, edges)
        if not forest:
            continue
        feasible_masks.append(mask)
        for u in isolates:
            assert not state[u]
            assert all(not state[w if v == u else v] for v, w in edges if u in (v, w))
        before = ledger(state, n, edges)
        after_state = exchange(state, n, selected)
        after = ledger(after_state, n, edges)
        assert {key: after[key]-before[key] for key in before} == deltas
    print(name, "variables", len(optional), "subsets", 1 << len(optional),
          "feasible extensions", len(feasible_masks), "all exchanges checked")
    return {"name": name, "n": n, "base_rows": rows(base, n),
            "levels": levels, "selected": selected, "patch": region,
            "protected_u": protected_u, "optional": optional,
            "base_ledger": base_ledger, "deltas": deltas,
            "subsets": 1 << len(optional), "feasible_masks": feasible_masks,
            "isolate_witnesses": isolates}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    with args.output.open("x") as output:
        original = rooted14()
        edges = grid_edges(14)
        before = ledger(original, 14, edges)
        assert tuple(before[k] for k in ("f", "r", "b", "c")) == (46, 7, 36, 71)
        final = exchange(original, 14, [4, 7, 10])
        after = ledger(final, 14, edges)
        assert [after[k]-before[k] for k in ("f", "r", "b", "c")] == [0, 2, 3, -5]
        fixtures = [
            run_fixture("rooted14_middle", 14, original, [4,7,10], [7], patch(14,9,5,5,5)),
            run_fixture("rooted14_cap", 14, original, [4,7,10], [7], patch(14,8,10,5,4)),
            run_fixture("rootless14_cap", 14, rootless14(), [4,7,10], [7], patch(14,8,10,5,4)),
            run_fixture("rooted15_cap", 15, rooted15(), [1,4,7,10], [4,7], patch(15,9,10,5,5)),
        ]
        # All three rootless teeth are in different actual components.
        labels, _, _ = components(rootless14(), grid_edges(14))
        assert len({labels[y*14+10] for y in [4,7,10]}) == 3
        json.dump({"schema": 1, "scope": "complete specified extension families; guarded exchanges, not global optimization",
                   "all_rows_control": {"before_rows": rows(original,14), "after_rows": rows(final,14),
                                        "before": before, "after": after, "selected": [4,7,10]},
                   "fixtures": fixtures}, output, indent=2)
        output.write("\n")


if __name__ == "__main__":
    main()
