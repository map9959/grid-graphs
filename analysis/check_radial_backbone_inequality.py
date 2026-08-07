"""Checks for the radial-backbone analysis.

This is deliberately independent of check_annular_merger_surplus.py.  It
models the outer and inner cycles explicitly, including the two spokes ending
at each inner corner.
"""

from __future__ import annotations

import argparse
import itertools


Vertex = tuple[int, int]
Edge = tuple[Vertex, Vertex]


class DSU:
    def __init__(self, vertices: list[Vertex]) -> None:
        self.parent = {vertex: vertex for vertex in vertices}

    def find(self, vertex: Vertex) -> Vertex:
        while self.parent[vertex] != vertex:
            self.parent[vertex] = self.parent[self.parent[vertex]]
            vertex = self.parent[vertex]
        return vertex

    def union(self, left: Vertex, right: Vertex) -> bool:
        left = self.find(left)
        right = self.find(right)
        if left == right:
            return False
        self.parent[right] = left
        return True


def grid_edges(n: int) -> list[Edge]:
    return [
        ((row, column), (row + 1, column))
        for row in range(n - 1)
        for column in range(n)
    ] + [
        ((row, column), (row, column + 1))
        for row in range(n)
        for column in range(n - 1)
    ]


def cycle(n: int, inset: int) -> list[Vertex]:
    low = inset
    high = n - 1 - inset
    return (
        [(low, column) for column in range(low, high + 1)]
        + [(row, high) for row in range(low + 1, high + 1)]
        + [(high, column) for column in range(high - 1, low - 1, -1)]
        + [(row, low) for row in range(high - 1, low, -1)]
    )


def annulus(n: int) -> tuple[list[Vertex], list[Vertex], list[Edge], list[Edge]]:
    outer = cycle(n, 0)
    inner = cycle(n, 1)
    outer_set = set(outer)
    inner_set = set(inner)
    edges = [
        edge
        for edge in grid_edges(n)
        if edge[0] in outer_set | inner_set and edge[1] in outer_set | inner_set
    ]
    spokes = [
        (left, right) if left in outer_set else (right, left)
        for left, right in edges
        if (left in outer_set) != (right in outer_set)
    ]
    return outer, inner, edges, spokes


def is_h_forest(vertices: list[Vertex], edges: list[Edge], u: set[Vertex]) -> bool:
    dsu = DSU(vertices)
    for left, right in edges:
        if left in u and right in u:
            continue
        if not dsu.union(left, right):
            return False
    return True


def backbone_count(
    boundary: list[Vertex], spokes: list[Edge], u: set[Vertex], f_only: bool
) -> int:
    dsu = DSU(boundary)
    for index, left in enumerate(boundary):
        right = boundary[(index + 1) % len(boundary)]
        active = left not in u and right not in u if f_only else not (left in u and right in u)
        if active:
            dsu.union(left, right)
    attached = set()
    for outer, inner in spokes:
        active = outer not in u and inner not in u if f_only else not (outer in u and inner in u)
        if active:
            attached.add(dsu.find(outer))
    return len(attached)


def radial_margin(n: int, u: set[Vertex]) -> tuple[int, tuple[int, int, int, int, int, int]]:
    outer, _, _, spokes = annulus(n)
    radial = [0, 0, 0, 0]  # UU, UF, FU, FF
    for outside, inside in spokes:
        radial[(outside not in u) * 2 + (inside not in u)] += 1
    a_h = backbone_count(outer, spokes, u, False)
    a_f = backbone_count(outer, spokes, u, True)
    r_uu, r_uf, r_fu, r_ff = radial
    return a_h + a_f + r_uu - r_uf - 2 * r_ff, (
        a_h,
        a_f,
        r_uu,
        r_uf,
        r_fu,
        r_ff,
    )


def annular_margin_three(n: int) -> set[Vertex]:
    outer, _, _, _ = annulus(n)
    return set(outer) | {(1, 1), (1, 2)}


def verify_obstruction(max_n: int) -> None:
    for n in range(5, max_n + 1):
        outer, inner, annular_edges, spokes = annulus(n)
        assert len(outer) == 4 * n - 4
        assert len(inner) == 4 * n - 12
        assert len(spokes) == 4 * n - 8
        multiplicities = {vertex: 0 for vertex in inner}
        for _, vertex in spokes:
            multiplicities[vertex] += 1
        corners = {(1, 1), (1, n - 2), (n - 2, 1), (n - 2, n - 2)}
        assert {vertex for vertex, count in multiplicities.items() if count == 2} == corners

        fixed_u = annular_margin_three(n)
        assert is_h_forest(outer + inner, annular_edges, fixed_u)
        margin, data = radial_margin(n, fixed_u)
        assert margin == 3, (n, margin, data)

        deep = [
            (row, column)
            for row in range(2, n - 2)
            for column in range(2, n - 2)
        ]
        if len(deep) > 20:
            continue
        full_vertices = [(row, column) for row in range(n) for column in range(n)]
        full_edges = grid_edges(n)
        completions = 0
        for labels in itertools.product((False, True), repeat=len(deep)):
            u = fixed_u | {vertex for vertex, label in zip(deep, labels) if label}
            completions += is_h_forest(full_vertices, full_edges, u)
        assert completions == 0, (n, completions)
        print(f"n={n}: annular margin 3; full completions 0/{1 << len(deep)}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-n", type=int, default=8)
    args = parser.parse_args()
    verify_obstruction(args.max_n)
