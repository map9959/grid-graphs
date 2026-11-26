"""Exact inverse-cross census for the fixed side-17 affine witness."""
from collections import Counter, defaultdict, deque
from itertools import product
from pathlib import Path


def load():
    path = Path(__file__).resolve().parents[1] / "residue_two_affine_17_witness.txt"
    rows = [s for s in path.read_text().splitlines() if not s.startswith("#")]
    assert len(rows) == 17 and all(len(s) == 17 for s in rows)
    return {(r, c) for r, row in enumerate(rows) for c, s in enumerate(row) if s == "."}


def grid(n):
    return product(range(n), repeat=2)


def geometry(n):
    # Coordinates on the doubled board; the exterior dual face is None.
    edges = {}
    for r, c in grid(n):
        for dr, dc in [(1, 0), (0, 1)]:
            if r+dr >= n or c+dc >= n:
                continue
            i, j = 2*r+dr, 2*c+dc
            faces = [(i-dc, j-dr), (i+dc, j+dr)]
            edges[i, j] = (((2*r, 2*c), (2*(r+dr), 2*(c+dc))),
                           tuple(p if min(p) >= 0 and max(p) < 2*n-1 else None for p in faces))
    return edges


def adjacency(edges, selected, dual=False):
    g = defaultdict(list)
    for m in selected:
        a, b = edges[m][int(dual)]
        g[a].append((b, m))
        g[b].append((a, m))
    return g


def parents(graph, root):
    seen = {root: None}
    stack = [root]
    while stack:
        for b, m in graph[stack.pop()]:
            if b not in seen:
                seen[b] = m
                stack.append(b)
    del seen[root]
    return seen


def tiling(edges, tree, root):
    orient = parents(adjacency(edges, tree), root)
    assert len(orient) == 288
    dual = parents(adjacency(edges, edges.keys()-tree, True), None)
    assert len(dual) == 256
    orient.update(dual)
    d = {}
    for (i, j), (a, b) in orient.items():
        assert (a, b) not in d
        d[i, j] = a-i, b-j
        d[a, b] = i-a, j-b
    assert len(d) == 33**2-1
    return d


def score(d, side):
    # Reconstruct the smaller primal tree independently of the cut test.
    n = (side+1)//2
    edges = geometry(n)
    tree = {m for m in edges if (m[0]+d[m][0]) % 2 == 0}
    assert len(tree) == n*n-1 and len(parents(adjacency(edges, tree), (0, 0))) == n*n-1
    lost = {p for m in edges.keys()-tree for p in edges[m][0]}
    return n*n-len(lost)


def repair_pair(d):
    """One deterministic shortest alternating path; keep all other dominoes."""
    free = [(i,j) for (i,j),(x,y) in d.items() if d.get((i+x,j+y)) != (-x,-y)]
    assert len(free) == 2
    s, t = sorted(free)
    queue = deque([s])
    prev = {s: None}
    while queue:
        u = queue.popleft()
        if u == t:
            break
        moves = [(0,1),(1,0),(0,-1),(-1,0)] if sum(u)%2 == sum(s)%2 else [d[u]]
        for x,y in moves:
            v = u[0]+x,u[1]+y
            if v in d and v not in prev:
                prev[v] = u
                queue.append(v)
    if t not in prev:
        return None
    path = [t]
    while path[-1] != s:
        path.append(prev[path[-1]])
    fixed = dict(d)
    for (i,j),(a,b) in zip(path[::2], path[1::2]):
        fixed[i,j], fixed[a,b] = (a-i,b-j),(i-a,j-b)
    assert all(fixed.get((i+x,j+y)) == (-x,-y) for (i,j),(x,y) in fixed.items())
    return len(path)//2, score(fixed, 21)


def periodic_tile(d, a, b):
    tile = {(i,j): d[a+i,b+j] for i,j in grid(12)}
    bad = [(i,j) for (i,j),(x,y) in tile.items()
           if tile[(i+x)%12,(j+y)%12] != (-x,-y)]
    if bad:
        return len(bad), None
    def primal(i,j):
        return (a+i+tile[i%12,j%12][0])%2 == 0
    f = sum(all(primal(i+x,j+y) for x,y in ((1,0),(-1,0),(0,1),(0,-1)))
            for i,j in tile if (a+i)%2 == (b+j)%2 == 0)
    return 0, f


def crop(d, a, b):
    return {(i-12*(i>=a+12),j-12*(j>=b+12)): v for (i,j),v in d.items()
            if not a <= i < a+12 and not b <= j < b+12}


def replay_chain():
    edges = geometry(17)
    centers = {(2*i,2*j) for i,j in load()}
    tree = {m for m,(p,_) in edges.items() if centers.intersection(p)} | {(3,4)}
    d = tiling(edges, tree, (0,0))
    scores = [score(d,33)]
    for a,b,i,j,side in [(7,7,6,13,21),(6,1,5,3,9)]:
        d = crop(d,a,b)
        free = {p for p,(x,y) in d.items() if d.get((p[0]+x,p[1]+y)) != (-x,-y)}
        assert free == {(i,j),(i,j+1)}
        d[i,j], d[i,j+1] = (0,1),(0,-1)
        scores.append(score(d,side))
    return scores


def census():
    centers = {(2*i, 2*j) for i, j in load()}
    edges = geometry(17)
    forced = {m for m, (p, _) in edges.items() if centers.intersection(p)}
    assert len(forced) == 287
    component = set(parents(adjacency(edges, forced), (0, 0))) | {(0, 0)}
    bridges = sorted(m for m, (p, _) in edges.items() if len(component.intersection(p)) == 1)
    cuts = range(1, 21)  # remove [a,a+12); both outer borders retained
    counts = Counter()
    examples = {}
    mismatches = Counter()
    repairs = Counter()
    tiles = Counter()
    for bridge, root in product(bridges, product((0, 32), repeat=2)):
        d = tiling(edges, forced | {bridge}, root)
        assert score(d, 33) == 110
        # Count dangling domino endpoints at a join, except on the perpendicular
        # strip, which disappears. Parity of the start is unrestricted.
        for a, b in product(cuts, repeat=2):
            bad = sum((d.get((a-1,j)) == (1,0)) != (d.get((a+12,j)) == (-1,0))
                      for j in range(33) if not b <= j < b+12)
            bad += sum((d.get((i,b-1)) == (0,1)) != (d.get((i,b+12)) == (0,-1))
                       for i in range(33) if not a <= i < a+12)
            mismatches[bad] += 1
            if bad <= 2:
                small = crop(d,a,b)
                if bad:
                    outcome = repair_pair(small)
                    repairs[outcome] += 1
                    if outcome:
                        examples.setdefault(outcome, (bridge, root, a, b))
                    if outcome == (1,48):
                        tiles[periodic_tile(d,a,b)] += 1
                    continue
                assert all(small.get((i+x,j+y)) == (-x,-y) for (i,j),(x,y) in small.items())
                f = score(small, 21)
                counts[f] += 1
                examples.setdefault(f, (bridge, root, a, b))
    return bridges, counts, examples, mismatches, repairs, tiles


if __name__ == "__main__":
    bridges, counts, examples, mismatches, repairs, tiles = census()
    print("completion midpoints:", bridges)
    print("cut tests:", sum(mismatches.values()), "valid by score:", sorted(counts.items()))
    print("examples (midpoint, root, row start, col start):", examples)
    print("unmatched endpoints:", sorted(mismatches.items()))
    print("shortest repairs (dominoes placed, score):", repairs)
    print("central tiles for one-domino target repairs (unmatched sites, score):", tiles)
    print("two-step score replay:", replay_chain())
