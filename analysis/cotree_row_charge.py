#!/usr/bin/env python3
"""Row/column census for cotree incidence waste of square-grid trees.

This is finite computational evidence, not a proof.  Edges are pairs of
row-major vertex numbers.  For a cotree C, ``cS`` denotes the number of
connected components of its support (isolated grid vertices are not counted).
"""

from __future__ import annotations

import argparse
import random
from dataclasses import dataclass
from functools import lru_cache
from itertools import combinations
from typing import Iterable, Iterator, Sequence


Edge = tuple[int, int]


class UnionFind:
    def __init__(self, size: int) -> None:
        self.parent = list(range(size))
        self.rank = [0] * size

    def root(self, vertex: int) -> int:
        while self.parent[vertex] != vertex:
            self.parent[vertex] = self.parent[self.parent[vertex]]
            vertex = self.parent[vertex]
        return vertex

    def union(self, left: int, right: int) -> bool:
        left, right = self.root(left), self.root(right)
        if left == right:
            return False
        if self.rank[left] < self.rank[right]:
            left, right = right, left
        self.parent[right] = left
        if self.rank[left] == self.rank[right]:
            self.rank[left] += 1
        return True


@lru_cache(maxsize=None)
def grid_edges(n: int) -> tuple[Edge, ...]:
    result = []
    for row in range(n):
        for column in range(n):
            vertex = row * n + column
            if column + 1 < n:
                result.append((vertex, vertex + 1))
            if row + 1 < n:
                result.append((vertex, vertex + n))
    return tuple(result)


def is_tree(vertex_count: int, edges: Sequence[Edge]) -> bool:
    if len(edges) != vertex_count - 1:
        return False
    forest = UnionFind(vertex_count)
    return all(forest.union(*edge) for edge in edges)


def spanning_trees(n: int) -> Iterator[tuple[Edge, ...]]:
    """Enumerate all trees; practical through 4x4 (100,352 trees)."""
    edges = grid_edges(n)
    for chosen in combinations(edges, n * n - 1):
        if is_tree(n * n, chosen):
            yield chosen


def random_spanning_tree(n: int, rng: random.Random) -> tuple[Edge, ...]:
    """Sample a uniform spanning tree using Wilson's loop-erased random walk."""
    vertex_count = n * n
    neighbors = [[] for _ in range(vertex_count)]
    for left, right in grid_edges(n):
        neighbors[left].append(right)
        neighbors[right].append(left)
    in_tree = {rng.randrange(vertex_count)}
    result: list[Edge] = []
    while len(in_tree) < vertex_count:
        start = next(vertex for vertex in range(vertex_count) if vertex not in in_tree)
        walk = [start]
        positions = {start: 0}
        while walk[-1] not in in_tree:
            nxt = rng.choice(neighbors[walk[-1]])
            if nxt in positions:
                keep = positions[nxt]
                for vertex in walk[keep + 1 :]:
                    positions.pop(vertex)
                walk = walk[: keep + 1]
            else:
                positions[nxt] = len(walk)
                walk.append(nxt)
        for left, right in zip(walk, walk[1:]):
            result.append(tuple(sorted((left, right))))
            in_tree.add(left)
    result.sort()
    assert is_tree(vertex_count, result)
    return tuple(result)


def extend_forced_set_to_tree(n: int, rows: Sequence[int], seed: int = 0) -> tuple[Edge, ...]:
    """Extend all edges incident to F to a tree, randomizing the other edges."""
    if len(rows) != n:
        raise ValueError("rows must encode an n by n set")
    forced = {
        edge
        for edge in grid_edges(n)
        if any((rows[v // n] >> (v % n)) & 1 for v in edge)
    }
    forest = UnionFind(n * n)
    result = []
    for edge in sorted(forced):
        if not forest.union(*edge):
            raise ValueError("the forced-edge graph is cyclic")
        result.append(edge)
    optional = [edge for edge in grid_edges(n) if edge not in forced]
    random.Random(seed).shuffle(optional)
    for edge in optional:
        if forest.union(*edge):
            result.append(edge)
    result.sort()
    assert is_tree(n * n, result)
    return tuple(result)


@dataclass(frozen=True)
class LineCharge:
    support: int
    parallel_edges: int
    previous_crossings: int
    next_crossings: int
    horizontal_components: int
    support_runs: int
    horizontal_gaps: int
    left_endpoints: int
    right_endpoints: int
    turns: int
    degree_deficit: int
    component_roots: int

    @property
    def waste(self) -> int:
        return (
            3 * self.support
            - 2 * self.parallel_edges
            - self.previous_crossings
            - self.next_crossings
        )


@dataclass(frozen=True)
class TreeProfile:
    n: int
    tree: tuple[Edge, ...]
    cotree: tuple[Edge, ...]
    support: int
    support_components: int
    cycle_rank: int
    waste: int
    rows: tuple[LineCharge, ...]
    columns: tuple[LineCharge, ...]

    @property
    def ocb_slack(self) -> int:
        return self.waste - (self.n + 1 + self.support_components)

    @property
    def cycle_excess_slack(self) -> int:
        """OCB in the support-excess/cycle-rank normal form."""
        return (
            self.support
            - self.n
            + self.support_components
            - 2 * self.cycle_rank
            - 1
        )


def _line_charges(n: int, cotree: Sequence[Edge], transpose: bool) -> tuple[LineCharge, ...]:
    degrees = [0] * (n * n)
    horizontal = [0] * n
    crossings = [0] * (n - 1)
    parallel_degree = [0] * (n * n)
    crossing_degree = [0] * (n * n)
    forest = UnionFind(n * n)
    for left, right in cotree:
        degrees[left] += 1
        degrees[right] += 1
        forest.union(left, right)
        lr, lc = divmod(left, n)
        rr, rc = divmod(right, n)
        if transpose:
            lr, lc, rr, rc = lc, lr, rc, rr
        if lr == rr:
            horizontal[lr] += 1
            parallel_degree[left] += 1
            parallel_degree[right] += 1
        else:
            strip = min(lr, rr)
            crossings[strip] += 1
            crossing_degree[left] += 1
            crossing_degree[right] += 1
    roots_by_line = [set() for _ in range(n)]
    root_first_line: dict[int, int] = {}
    for vertex, degree in enumerate(degrees):
        if not degree:
            continue
        row, column = divmod(vertex, n)
        line, position = (column, row) if transpose else (row, column)
        root = forest.root(vertex)
        roots_by_line[line].add(root)
        root_first_line[root] = min(line, root_first_line.get(root, line))
    result = []
    for line in range(n):
        vertices = [
            (position * n + line if transpose else line * n + position)
            for position in range(n)
        ]
        supported_positions = [position for position, v in enumerate(vertices) if degrees[v]]
        parallel_components = len(supported_positions) - horizontal[line]
        left_endpoints = sum(
            position == 0 or not degrees[vertices[position - 1]]
            for position in supported_positions
        )
        right_endpoints = sum(
            position == n - 1 or not degrees[vertices[position + 1]]
            for position in supported_positions
        )
        support_runs = left_endpoints
        turns = sum(
            bool(parallel_degree[v]) and bool(crossing_degree[v]) for v in vertices
        )
        result.append(
            LineCharge(
                support=len(supported_positions),
                parallel_edges=horizontal[line],
                previous_crossings=crossings[line - 1] if line else 0,
                next_crossings=crossings[line] if line + 1 < n else 0,
                horizontal_components=parallel_components,
                support_runs=support_runs,
                horizontal_gaps=parallel_components - support_runs,
                left_endpoints=left_endpoints,
                right_endpoints=right_endpoints,
                turns=turns,
                degree_deficit=sum(3 - degrees[v] for v in vertices if degrees[v]),
                component_roots=sum(first == line for first in root_first_line.values()),
            )
        )
    return tuple(result)


def profile(n: int, tree: Iterable[Edge]) -> TreeProfile:
    tree = tuple(sorted(tuple(sorted(edge)) for edge in tree))
    all_edges = grid_edges(n)
    all_edge_set = set(all_edges)
    if not is_tree(n * n, tree) or any(edge not in all_edge_set for edge in tree):
        raise ValueError("input is not an n by n grid spanning tree")
    tree_set = set(tree)
    cotree = tuple(edge for edge in all_edges if edge not in tree_set)
    degrees = [0] * (n * n)
    forest = UnionFind(n * n)
    for edge in cotree:
        degrees[edge[0]] += 1
        degrees[edge[1]] += 1
        forest.union(*edge)
    support_vertices = [vertex for vertex, degree in enumerate(degrees) if degree]
    components = len({forest.root(vertex) for vertex in support_vertices})
    cycle_rank = len(cotree) - len(support_vertices) + components
    waste = sum(3 - degrees[vertex] for vertex in support_vertices)
    result = TreeProfile(
        n=n,
        tree=tree,
        cotree=cotree,
        support=len(support_vertices),
        support_components=components,
        cycle_rank=cycle_rank,
        waste=waste,
        rows=_line_charges(n, cotree, False),
        columns=_line_charges(n, cotree, True),
    )
    assert len(cotree) == (n - 1) ** 2
    assert waste == 3 * result.support - 2 * len(cotree)
    assert waste == result.support + 2 * components - 2 * cycle_rank
    assert result.ocb_slack == result.cycle_excess_slack
    for lines in (result.rows, result.columns):
        assert waste == sum(line.waste for line in lines)
        for line in lines:
            assert line.waste == line.degree_deficit
            assert line.support - line.parallel_edges == line.horizontal_components
            assert line.left_endpoints == line.right_endpoints == line.support_runs
            assert line.waste == (
                line.support
                + 2 * line.horizontal_components
                - line.previous_crossings
                - line.next_crossings
            )
            assert line.waste == (
                line.support
                + line.left_endpoints
                + line.right_endpoints
                + 2 * line.horizontal_gaps
                - line.previous_crossings
                - line.next_crossings
            )
    return result


def summarize(items: Iterable[TreeProfile], label: str) -> tuple[int, TreeProfile]:
    count = 0
    best: TreeProfile | None = None
    minimum_line = 10**9
    minimum_root_line = 10**9
    minimum_prefix = 10**9
    for item in items:
        count += 1
        if best is None or item.ocb_slack < best.ocb_slack:
            best = item
        for lines in (item.rows, item.columns):
            minimum_line = min(minimum_line, *(line.waste for line in lines))
            minimum_root_line = min(
                minimum_root_line,
                *(line.waste - line.component_roots - 1 for line in lines),
            )
            running = 0
            for line in lines:
                running += line.waste - line.component_roots - 1
                minimum_prefix = min(minimum_prefix, running)
    if best is None:
        raise ValueError("empty census")
    print(
        f"{label}: trees={count} min_ocb_slack={best.ocb_slack} "
        f"min_line_waste={minimum_line} min(w-root-1)={minimum_root_line} "
        f"min_prefix(w-root-1)={minimum_prefix}"
    )
    if best.ocb_slack < 0:
        print(f"  OCB FALSIFIER tree={best.tree}")
    return count, best


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exhaustive-n", type=int, default=4)
    parser.add_argument("--random-n", type=int, default=12)
    parser.add_argument("--random-count", type=int, default=1000)
    parser.add_argument("--seed", type=int, default=20260814)
    parser.add_argument("--maximum-n", type=int, default=9)
    parser.add_argument("--maximum-limit", type=int, default=100)
    args = parser.parse_args()
    for n in range(2, args.exhaustive_n + 1):
        summarize((profile(n, tree) for tree in spanning_trees(n)), f"n={n} exhaustive")
    rng = random.Random(args.seed)
    for n in range(max(5, args.exhaustive_n + 1), args.random_n + 1):
        summarize(
            (profile(n, random_spanning_tree(n, rng)) for _ in range(args.random_count)),
            f"n={n} Wilson",
        )
    if args.maximum_n:
        from max_fr_checker import maximum_witnesses

        for n in range(3, args.maximum_n + 1):
            trees = (
                profile(n, extend_forced_set_to_tree(n, rows, index))
                for index, rows in enumerate(maximum_witnesses(n, args.maximum_limit))
            )
            summarize(trees, f"n={n} maximum-F")


if __name__ == "__main__":
    main()
