"""Diagnostic only: test whether a compact rooted bulk window forces masks.

The right, left, and bottom sides are open. Contract the already rooted
top tips to one vertex when testing the physical forest condition.
No solver traces are written.
"""
from functools import lru_cache
from itertools import combinations, product

from analysis.research_program.defect_window import DIR, table
from analysis.research_program.tight_corner_sat import cover
from pysat.solvers import Solver

SHAPES = {9, 72, 73, 2, 66, 16, 128, 129, 132, 36, 258, 288, 292}


def probe(height=30, width=30, y=4, x=3, want=SHAPES, plateau=1):
    typ, patch, star = table(35)
    sites = list(product(range(height), range(width)))
    size = len(sites)

    def bit(r, c):
        return r * width + c + 1

    def arc(r, c, d):
        return size + 4 * (bit(r, c) - 1) + d + 1

    def inside(r, c):
        return 0 <= r < height and 0 <= c < width

    @lru_cache(None)
    def banned(prices):
        return cover(tuple(p != 0 for p in prices))

    with Solver(name="cadical195") as sat:
        def exclude(vs, guard, cs):
            for mask, value in cs:
                sat.add_clause(guard + [(-v if value >> k & 1 else v)
                                       for k, v in enumerate(vs) if mask >> k & 1])

        def bits(r, c):
            return [bit(r + i, c + j) for i, j in product(range(3), repeat=2)]

        edges = []
        for r, c in sites:
            v = bit(r, c)
            ds = range(4)
            arcs = [arc(r, c, d) for d in ds]
            sat.add_clause(arcs)
            for a, b in combinations(arcs, 2):
                sat.add_clause([-a, -b])
            if r < 3 * plateau:
                sat.add_clause([v if c % 3 == 0 else -v])
            if r == 0:
                sat.add_clause([arcs[3] if c % 3 == 0 else -arcs[3]])
            if r + 2 < height and c + 2 < width:
                exclude(bits(r, c), [], banned(patch(typ(1, 7 + r % 3, 7 + c % 3))))
            for d, (dr, dc) in enumerate(DIR):
                if d < 2 and inside(r + dr, c + dc):
                    w = bit(r + dr, c + dc)
                    a, b = arcs[d], arc(r + dr, c + dc, d + 2)
                    edges.append((v, w, a, b))
                    for clause in ([-a, -b], [-v, a, b], [-w, a, b],
                                   [-a, v, w], [-b, v, w]):
                        sat.add_clause(clause)
            near = [(r + dr, c + dc) for dr, dc in DIR]
            if all(inside(*p) for p in near):
                s = typ(0, 8 + (r - 1) % 3, 8 + (c - 1) % 3)
                for d in ds:
                    exclude([v, *map(lambda p: bit(*p), near)], [-arcs[d]],
                            banned(star(s, tuple(ds), d, False, False)))

        exclude(bits(3 * y, 3 * x), [], cover(tuple(m in want for m in range(512))))
        for attempts in range(256):
            if not sat.solve():
                return None
            yes = {a for a in sat.get_model() if a > 0}
            g = [[] for _ in range(size + 1)]
            for c in range(0, width, 3):
                u = bit(0, c)
                g[0].append((u, 0))
                g[u].append((0, 0))
            for v, w, a, b in edges:
                edge = a if a in yes else b if b in yes else 0
                if edge:
                    g[v].append((w, edge))
                    g[w].append((v, edge))
            parent = {}
            cyclic = False
            for u in range(size + 1):
                if u in parent:
                    continue
                parent[u] = (-1, 0)
                todo = [u]
                while todo:
                    v = todo.pop()
                    for w, e in g[v]:
                        if parent[v][0] == w or parent.get(w, (-1, 0))[0] == v:
                            continue
                        if w not in parent:
                            parent[w] = (v, e)
                            todo.append(w)
                            continue
                        p = {}
                        a, cycle = v, [e]
                        while a >= 0:
                            p[a] = cycle.copy()
                            a, e = parent[a]
                            cycle.append(e)
                        a, cycle = w, []
                        while a not in p:
                            a, e = parent[a]
                            cycle.append(e)
                        sat.add_clause([-e for e in cycle + p[a] if e])
                        cyclic = True
                if cyclic:
                    break
            if not cyclic:
                mask = sum((v in yes) << k for k, v in enumerate(bits(3 * y, 3 * x)))
                return mask, ["".join(str(int(bit(r, c) in yes)) for c in range(width))
                              for r in range(height)], [
                                  "".join(str(next(d for d in range(4) if arc(r, c, d) in yes))
                                          for c in range(width)) for r in range(height)]
        raise RuntimeError("cycle-cut diagnostic budget exhausted")


if __name__ == "__main__":
    import sys
    h, w, y, x = map(int, sys.argv[1:5])
    z = probe(h, w, y, x, {73} if "step" in sys.argv else SHAPES)
    print("UNSAT" if z is None else ("forest mask", z[0]), flush=True)
    if z and "show" in sys.argv:
        print("\n".join(z[1] + [""] + z[2]))
