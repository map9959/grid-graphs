#!/usr/bin/env python3
r"""Verify explicit diagonal U-pattern constructions.

This is a lightweight checker for candidate parametric diagonal constructions.
It does not run the frontier DP. Given a generated non-full set U, it:

1. forces every grid edge touching F = V \ U,
2. checks those forced edges are acyclic,
3. greedily completes the forest using U-U edges,
4. verifies the completed tree has the claimed number of full-degree vertices.

The n ≡ 1 mod 3 infinite family and all cached exact residue-0/2 witnesses from
`diagonal_patterns.py` are checked.
"""

from __future__ import annotations

import argparse

from construction_lab import dual_connectivity_check
from diagonal_patterns import (
    STATUS_RESIDUE_TWO,
    STATUS_RESIDUE_ZERO,
    q_formula,
    residue_one_pattern,
    residue_two_explicit_pattern,
    residue_zero_explicit_pattern,
    residue_zero_improved_pattern,
    residue_zero_phase_pattern,
    residue_zero_pattern,
)


class DSU:
    def __init__(self, n: int):
        self.parent = list(range(n))

    def find(self, x: int) -> int:
        while self.parent[x] != x:
            self.parent[x] = self.parent[self.parent[x]]
            x = self.parent[x]
        return x

    def union(self, a: int, b: int) -> bool:
        ra, rb = self.find(a), self.find(b)
        if ra == rb:
            return False
        self.parent[rb] = ra
        return True


def grid_edges(n: int):
    for r in range(n):
        for c in range(n):
            a = r * n + c
            if c + 1 < n:
                yield a, a + 1, ((r, c), (r, c + 1))
            if r + 1 < n:
                yield a, a + n, ((r, c), (r + 1, c))


def grid_degree(n: int, r: int, c: int) -> int:
    return (r > 0) + (r + 1 < n) + (c > 0) + (c + 1 < n)


def verify_pattern(rows: list[str]) -> tuple[int, int, int]:
    n = len(rows)
    if not all(len(row) == n for row in rows):
        raise ValueError("pattern must be square")
    if any(value not in ".U" for row in rows for value in row):
        raise ValueError("pattern entries must be '.' or 'U'")
    is_u = [ch == "U" for row in rows for ch in row]
    is_full = [not x for x in is_u]
    dsu = DSU(n * n)
    forced_edges: list[tuple[tuple[int, int], tuple[int, int]]] = []
    optional_edges: list[tuple[int, int, tuple[tuple[int, int], tuple[int, int]]]] = []

    for a, b, edge in grid_edges(n):
        if is_full[a] or is_full[b]:
            if not dsu.union(a, b):
                raise AssertionError("forced edges contain a cycle")
            forced_edges.append(edge)
        else:
            optional_edges.append((a, b, edge))

    tree_edges = list(forced_edges)
    for a, b, edge in optional_edges:
        if dsu.union(a, b):
            tree_edges.append(edge)

    if len(tree_edges) != n * n - 1:
        raise AssertionError(f"completion has {len(tree_edges)} edges, expected {n*n-1}")

    root = dsu.find(0)
    if any(dsu.find(v) != root for v in range(n * n)):
        raise AssertionError("completion is disconnected")

    deg = [0] * (n * n)
    for (r1, c1), (r2, c2) in tree_edges:
        deg[r1 * n + c1] += 1
        deg[r2 * n + c2] += 1
    full_count = 0
    for r in range(n):
        for c in range(n):
            if deg[r * n + c] == grid_degree(n, r, c):
                full_count += 1

    return sum(is_u), full_count, len(tree_edges)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("nmax", type=int, nargs="?", default=40)
    args = parser.parse_args()
    if residue_zero_phase_pattern(21) != residue_zero_explicit_pattern(21):
        raise AssertionError("phase-family base no longer matches cached n=21")
    for n in range(6, args.nmax + 1, 3):
        improved = residue_zero_improved_pattern(n)
        nonfull, _, _ = verify_pattern(improved)
        expected = q_formula(n) + n // 3 - 2
        if nonfull != expected:
            raise AssertionError(
                f"improved residue-zero count at n={n}: {nonfull}, expected {expected}"
            )
    print("n,nonfull,expected_nonfull,full,expected_full,edges,status")
    for n in range(4, args.nmax + 1):
        if n % 3 == 1:
            rows = residue_one_pattern(n)
        elif n in STATUS_RESIDUE_TWO:
            rows = residue_two_explicit_pattern(n)
        elif n in STATUS_RESIDUE_ZERO:
            rows = residue_zero_explicit_pattern(n)
        elif n % 3 == 0 and n >= 21:
            rows = residue_zero_pattern(n)
        else:
            continue
        nonfull, full, edges = verify_pattern(rows)
        dual_ok, _, _ = dual_connectivity_check(rows)
        expected_nonfull = q_formula(n)
        expected_full = n * n - expected_nonfull
        status = (
            nonfull == expected_nonfull
            and full == expected_full
            and edges == n * n - 1
            and dual_ok
        )
        print(f"{n},{nonfull},{expected_nonfull},{full},{expected_full},{edges},{status}")
        if not status:
            raise SystemExit(1)


if __name__ == "__main__":
    main()
