#!/usr/bin/env python3
"""Exhaustively check full-degree spanning-tree identities on small grids."""

from __future__ import annotations

import argparse
import itertools


def grid_edges(n: int) -> list[tuple[int, int]]:
    edges: list[tuple[int, int]] = []
    for r in range(n):
        for c in range(n):
            v = r * n + c
            if r + 1 < n:
                edges.append((v, v + n))
            if c + 1 < n:
                edges.append((v, v + 1))
    return edges


def is_tree(vertex_count: int, edges: tuple[tuple[int, int], ...]) -> bool:
    parent = list(range(vertex_count))

    def root(v: int) -> int:
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v

    for a, b in edges:
        ra, rb = root(a), root(b)
        if ra == rb:
            return False
        parent[ra] = rb
    return True  # There are vertex_count - 1 edges.


def check_width(n: int) -> None:
    all_edges = grid_edges(n)
    vertex_count = n * n
    grid_degree = [0] * vertex_count
    for a, b in all_edges:
        grid_degree[a] += 1
        grid_degree[b] += 1

    count = 0
    minimum_waste: int | None = None
    minimum_full = -1
    witness: tuple[tuple[int, int], ...] | None = None

    for chosen in itertools.combinations(all_edges, vertex_count - 1):
        if not is_tree(vertex_count, chosen):
            continue
        count += 1
        tree_degree = [0] * vertex_count
        chosen_set = set(chosen)
        for a, b in chosen:
            tree_degree[a] += 1
            tree_degree[b] += 1

        full = {v for v in range(vertex_count) if tree_degree[v] == grid_degree[v]}
        support = set(range(vertex_count)) - full
        q_total = sum(4 - grid_degree[v] for v in support)
        slot_total = sum(tree_degree[v] - 1 for v in support)
        waste = q_total + slot_total
        omitted = [edge for edge in all_edges if edge not in chosen_set]
        omitted_degree = [0] * vertex_count
        for a, b in omitted:
            omitted_degree[a] += 1
            omitted_degree[b] += 1

        n1 = sum(degree == 1 for degree in omitted_degree)
        n2 = sum(degree == 2 for degree in omitted_degree)
        perimeter_omissions = sum(
            (a // n in (0, n - 1) and b // n == a // n)
            or (a % n in (0, n - 1) and b % n == a % n)
            for a, b in omitted
        )

        assert len(omitted) == (n - 1) ** 2
        assert sum(omitted_degree) == 2 * (n - 1) ** 2
        assert waste == 2 * n1 + n2
        assert 3 * len(support) - 2 * (n - 1) ** 2 == waste
        assert 3 * len(full) == n * n + 4 * n - 2 - waste
        assert q_total >= perimeter_omissions

        if minimum_waste is None or waste < minimum_waste:
            minimum_waste = waste
            minimum_full = len(full)
            witness = chosen

    assert minimum_waste is not None and witness is not None
    proposed_holds = minimum_waste >= n + 2
    print(
        f"n={n}: trees={count}, min(Q+S)={minimum_waste}, "
        f"max|F|={minimum_full}, target={n + 2}, holds={proposed_holds}"
    )
    print(f"  minimum-waste tree edges={witness}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--max-n",
        type=int,
        default=3,
        help="largest width (4 is exhaustive but substantially slower)",
    )
    args = parser.parse_args()
    if args.max_n < 2:
        parser.error("--max-n must be at least 2")
    for n in range(2, args.max_n + 1):
        check_width(n)


if __name__ == "__main__":
    main()
