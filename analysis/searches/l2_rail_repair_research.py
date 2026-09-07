#!/usr/bin/env python3
"""Bounded terminal-rail experiments; no external solver or project build.

Coordinates reproduce ResidueTwoStaircase.lean. All graph vertices, including
isolates, are retained. Search is exhaustive only in the printed variable set.
Run explicitly with python3 -m analysis.searches.l2_rail_repair_research.
"""

from itertools import product


def staircase(s):
    n = 3 * s + 5
    if not 2 <= s or n > 15:
        raise ValueError("experiments require 2 <= s and n <= 15")
    holes = {(0, 1), (0, 2), (1, n - 1), (n - 1, n - 2), (n - 2, 0)}
    frame = {(r, c) for r, c in product(range(n), repeat=2)
             if r in (0, n - 1) or c in (0, n - 1)} - holes
    rails = {(2, 2)}
    rails |= {(3 * j + 3, c) for j in range(s)
              for c in range(j + 4, 3 * s + 3)}
    rails |= {(3 * j + 5, c) for j in range(s - 1)
              for c in range(2, j + 4)}
    pocket = {(3 * s + 2, s + 2 - 4 * t) for t in range((s + 3) // 4)}
    pocket |= {(3 * s + 1, s - 4 * t) for t in range((s + 1) // 4)}
    return n, frame | rails | pocket


def neighbors(n, v):
    r, c = v
    return [(a, b) for a, b in ((r - 1, c), (r + 1, c), (r, c - 1), (r, c + 1))
            if 0 <= a < n and 0 <= b < n]


def root(parent, v):
    while parent[v] != v:
        v = parent[v]
    return v


def join(parent, a, b):
    a, b = root(parent, a), root(parent, b)
    if a == b:
        return False
    parent[b] = a
    return True


def forced_partition(n, centers):
    assert n <= 15
    parent = {v: v for v in product(range(n), repeat=2)}
    for v in sorted(parent):
        for w in neighbors(n, v):
            if v < w and (v in centers or w in centers):
                if not join(parent, v, w):
                    raise ValueError("forced cycle")
    return parent


def insert(n, centers, parent, v):
    assert v not in centers
    attachments = [v] + [w for w in neighbors(n, v) if w not in centers]
    labels = [root(parent, w) for w in attachments]
    if len(set(labels)) != len(labels):
        return None
    result = parent.copy()
    for w in attachments[1:]:
        assert join(result, v, w)
    return result


def maximize(n, fixed, variable):
    """Exact monotone search, retaining all actual component identifications."""
    initial = forced_partition(n, fixed)
    best = set()
    nodes = 0

    def visit(centers, parent, choices, added):
        nonlocal best, nodes
        nodes += 1
        if len(added) > len(best):
            best = added.copy()
        if len(added) + len(choices) <= len(best):
            return
        legal = [(v, p) for v in choices if (p := insert(n, centers, parent, v)) is not None]
        while legal:
            if len(added) + len(legal) <= len(best):
                break
            v, p = legal.pop(0)
            visit(centers | {v}, p, [w for w, _ in legal], added | {v})

    visit(set(fixed), initial, sorted(set(variable) - fixed), set())
    forced_partition(n, fixed | best)
    return best, nodes


def profile(n, centers):
    p = forced_partition(n, centers)
    c = len({root(p, v) for v in p})
    induced_edges = sum(v < w and w in centers for v in centers for w in neighbors(n, v))
    r = len(centers) - induced_edges
    b = sum(4 - len(neighbors(n, v)) for v in p if v not in centers)
    assert 3 * len(centers) + r + c + b == n * n + 4 * n
    return {"f": len(centers), "r": r, "c": c, "b": b}


def repaired_staircase(s):
    n, original = staircase(s)
    h = 3 * s
    pocket = {(r, c) for r in (h + 1, h + 2) for c in range(2, h + 3)}
    fixed = original - pocket - {(h, c) for c in range(s + 3, s + 6)}
    pieces = [ {(h - 1, s + 4)},
               {(h + 1, c) for c in range(s + 1, s + 4)},
               {(h + 2, s + 5)} ]
    pieces += [{(h + 2 - (t % 2), c)}
               for t, c in enumerate(range(s - 1, 2, -2))]
    return n, fixed, pieces


def audit_insertions(n, fixed, pieces):
    centers = fixed.copy()
    parent = forced_partition(n, centers)
    signatures = []
    for piece in pieces:
        for v in sorted(piece):
            attachments = [v] + [w for w in neighbors(n, v) if w not in centers]
            sizes = [sum(root(parent, x) == root(parent, w) for x in parent)
                     for w in attachments]
            updated = insert(n, centers, parent, v)
            assert updated is not None, (v, attachments)
            signatures.append((v, sizes))
            parent = updated
            centers.add(v)
    # Reconstruct all forced edges independently of the insertion order.
    rebuilt = forced_partition(n, centers)
    assert all((root(parent, v) == root(parent, w)) ==
               (root(rebuilt, v) == root(rebuilt, w)) for v in parent for w in parent)
    return centers, signatures


def check_support_invariant(n, s, fixed, pieces):
    def support(centers):
        return centers | {w for v in centers for w in neighbors(n, v)}

    old = support(fixed)
    h = 3 * s
    expected = [(h - 2, s + 4), (h, s + 1), (h + 3, s + 5)]
    expected += [(h + 3 if t % 2 == 0 else h, c)
                 for t, c in enumerate(range(s - 1, 2, -2))]
    supports = [support(piece) for piece in pieces]
    for i, vertices in enumerate(supports):
        assert vertices & old == {expected[i]}
        assert all(vertices.isdisjoint(other) for other in supports[:i])


def main():
    for s in (2, 3):
        n, original = staircase(s)
        h = 3 * s
        assert profile(n, original) == {"f": 48 if s == 2 else 76,
                                        "r": 9 if s == 2 else 12, "c": 7, "b": 5}
        print("seed", s, n, profile(n, original), flush=True)
        _, fixed, pieces = repaired_staircase(s)
        check_support_invariant(n, s, fixed, pieces)
        repaired, signatures = audit_insertions(n, fixed, pieces)
        assert len(repaired) == 3 * s * s + 12 * s + 12 + s // 2
        print("uniform-motif", profile(n, repaired), "insertions (component sizes)",
              signatures, flush=True)
        pocket = {(r, c) for r in (h + 1, h + 2) for c in range(2, h + 3)}
        detached = original - pocket - {(h, h + 2)}
        best, nodes = maximize(n, detached, pocket)
        assert len(detached | best) == len(original)
        print("endpoint-detached-pocket", "nodes", nodes,
              "profile", profile(n, detached | best), "pocket", sorted(best), flush=True)
        # The two nontrivial components must really be different before insertion.
        p = forced_partition(n, detached)
        v = (h + 2, h + 1)
        assert root(p, (h + 1, h + 1)) != root(p, (h + 3, h + 1))
        _, signatures = audit_insertions(n, detached, [{v}])
        print("rootless-bridge", signatures, flush=True)
        variable = {(r, c) for r in range(h - 1, h + 3) for c in range(2, h + 3)}
        for detach in (False, True):
            removed = {(h, h + 4)} if detach else set()
            fixed = original - variable - removed
            best, nodes = maximize(n, fixed, variable)
            repaired = fixed | best
            assert len(repaired) == (49 if s == 2 and not detach else len(original))
            print("terminal-four", "detach", detach, "nodes", nodes,
                  "profile", profile(n, repaired),
                  "delete", sorted(original - repaired),
                  "insert", sorted(repaired - original), flush=True)


if __name__ == "__main__":
    main()
