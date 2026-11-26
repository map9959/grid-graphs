"""Bounded checks of count-balanced seams, not a general lower-bound search."""

from itertools import product

from analysis.searches.l2_rail_repair_research import (
    forced_partition, insert, neighbors, profile, root, staircase,
)


def seam(s, phases):
    n, source = staircase(s)  # Rejects every board above side 15.
    if (len(phases) != s or phases[0] != 2
            or any(not 2 <= a <= 3 * s for a in phases)
            or any(b > a + 1 for a, b in zip(phases, phases[1:]))):
        raise ValueError("invalid seam phases")
    frame = {v for v in source if 0 in v or n - 1 in v}
    centers = frame.copy()
    for j, a in enumerate(phases):
        centers.update((3 * j + 2, c) for c in range(2, a + 1))
        centers.update((3 * j + 3, c) for c in range(a + 2, 3 * s + 3))
    return n, centers


def probe(s, node_cap=1000):
    """Enumerate phase prefixes; stop strictly before exceeding node_cap."""
    staircase(s)
    if not 1 <= node_cap <= 1000:
        raise ValueError("node cap must be in [1,1000]")
    nodes = layouts = exposed = 0
    exhaustive = True

    def visit(phases):
        nonlocal nodes, layouts, exposed, exhaustive
        if nodes == node_cap:
            exhaustive = False
            return
        nodes += 1
        if len(phases) < s:
            for a in range(2, phases[-1] + 2):
                visit(phases + (a,))
                if not exhaustive:
                    return
            return
        n, centers = seam(s, phases)
        parent = forced_partition(n, centers)
        assert len(centers) == 3 * s * s + 12 * s + 11
        deep = {v for v in centers if all(2 <= x <= n - 3 for x in v)}
        ff = sum(v < w and w in deep for v in deep for w in neighbors(n, v))
        assert ff == 3 * s * s - 2 * s
        for j, (a, b) in enumerate(zip(phases, phases[1:])):
            for c in range(b + 2, a + 1):
                v = (3 * j + 4, c)
                assert all(w not in centers for w in neighbors(n, v))
                assert insert(n, centers, parent, v) is None
                exposed += 1
        layouts += 1

    visit((2,))
    return dict(s=s, n=3 * s + 5, node_cap=node_cap, nodes=nodes,
                exhaustive=exhaustive, layouts=layouts, exposed=exposed)


def collision_motif():
    """An 11-board four-rod replay with a nonempty descending seam."""
    n, source = staircase(2)
    centers = {v for v in source if 0 in v or n - 1 in v}
    for r, lo, hi in ((3, 2, 5), (4, 7, 8), (6, 2, 2), (7, 4, 8)):
        centers.update((r, c) for c in range(lo, hi + 1))
    parent = forced_partition(n, centers)
    v = (5, 4)
    ports = [v] + neighbors(n, v)
    blocks = {}
    for w in ports:
        blocks.setdefault(root(parent, w), []).append(w)
    assert insert(n, centers, parent, v) is None
    assert all(w not in centers for w in neighbors(n, v))
    assert sum(root(parent, w) == root(parent, v)
               for w in product(range(n), repeat=2)) == 1
    return profile(n, centers), sorted(sorted(block) for block in blocks.values())


if __name__ == "__main__":
    for size in (2, 3):
        print(probe(size))
    print("four-rod collision", collision_motif())
