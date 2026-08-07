#!/usr/bin/env python3
"""Exact forest-component reduction for residue-two obligation 5.

This module checks identities only.  It does not prove the remaining geometric
component inequality.
"""

from __future__ import annotations

from dataclasses import dataclass


class _DSU:
    def __init__(self, size: int) -> None:
        self.parent = list(range(size))

    def find(self, vertex: int) -> int:
        while self.parent[vertex] != vertex:
            self.parent[vertex] = self.parent[self.parent[vertex]]
            vertex = self.parent[vertex]
        return vertex

    def union(self, left: int, right: int) -> bool:
        left = self.find(left)
        right = self.find(right)
        if left == right:
            return False
        self.parent[right] = left
        return True


@dataclass(frozen=True, slots=True)
class ComponentReduction:
    n: int
    u_count: int
    full_count: int
    boundary_u: int
    full_components: int
    forced_components: int
    full_edges: int
    forced_edges: int
    curvature: int

    @property
    def component_charge(self) -> int:
        return self.boundary_u + self.full_components + self.forced_components


def _validate(rows: list[str]) -> int:
    if len(rows) < 2 or any(len(row) != len(rows) for row in rows):
        raise ValueError("pattern must be a square of side at least two")
    if any(set(row) - {"U", "."} for row in rows):
        raise ValueError("pattern may contain only U and .")
    return len(rows)


def check_component_reduction(rows: list[str]) -> ComponentReduction:
    """Check the exact component decomposition when the forced graph is a forest."""
    n = _validate(rows)
    size = n * n
    full_dsu = _DSU(size)
    forced_dsu = _DSU(size)
    full_edges = forced_edges = 0

    def index(row: int, column: int) -> int:
        return row * n + column

    for row in range(n):
        for column in range(n):
            for d_row, d_column in ((0, 1), (1, 0)):
                other_row = row + d_row
                other_column = column + d_column
                if other_row == n or other_column == n:
                    continue
                left_full = rows[row][column] == "."
                right_full = rows[other_row][other_column] == "."
                if left_full and right_full:
                    full_edges += 1
                    full_dsu.union(index(row, column), index(other_row, other_column))
                if left_full or right_full:
                    forced_edges += 1
                    if not forced_dsu.union(index(row, column), index(other_row, other_column)):
                        raise ValueError("forced graph G-E(G[U]) is not a forest")

    full_vertices = [
        index(row, column)
        for row in range(n)
        for column in range(n)
        if rows[row][column] == "."
    ]
    full_count = len(full_vertices)
    u_count = size - full_count
    full_components = len({full_dsu.find(vertex) for vertex in full_vertices})
    forced_components = len({forced_dsu.find(vertex) for vertex in range(size)})
    boundary_u = sum(
        rows[row][column] == "U"
        for row in range(n)
        for column in range(n)
        for _ in range((row in (0, n - 1)) + (column in (0, n - 1)))
    )
    curvature = 3 * u_count - 2 * (n - 1) ** 2 - n

    if full_edges != full_count - full_components:
        raise AssertionError("the induced full-vertex graph is not a forest")
    if forced_edges != size - forced_components:
        raise AssertionError("forced-forest component identity failed")
    if curvature != boundary_u + full_components + forced_components - n - 2:
        raise AssertionError("obligation-5 component decomposition failed")

    return ComponentReduction(
        n=n,
        u_count=u_count,
        full_count=full_count,
        boundary_u=boundary_u,
        full_components=full_components,
        forced_components=forced_components,
        full_edges=full_edges,
        forced_edges=forced_edges,
        curvature=curvature,
    )
