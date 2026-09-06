#!/usr/bin/env python3
"""Exhaust coordinated exchanges around the best stochastic n=21 near-hit."""

from __future__ import annotations

import argparse
from itertools import combinations

from analysis.patterns.construction_lab import run_check
from analysis.searches.search_residue_anneal import (
    NEAR_N21,
    bits_to_rows,
    bridge_additions,
    dual_metrics,
    rows_to_bits,
    u_degree,
)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--patch-height", type=int, default=4)
    parser.add_argument("--patch-width", type=int, default=5)
    parser.add_argument("--skip-exchange", action="store_true")
    args = parser.parse_args()

    n = 21
    bits = rows_to_bits(NEAR_N21)
    baseline = dual_metrics(bits, n)
    if baseline.score != (1, 1, 0):
        raise AssertionError(f"near-hit metrics changed: {baseline.score}")

    dots = [vertex for vertex in range(n * n) if not bits & (1 << vertex)]
    bridge_options = bridge_additions(bits, n, baseline)
    additions = set()
    for option in bridge_options:
        if len(option) == 2:
            additions.add(tuple(sorted(option)))
        elif len(option) == 1:
            for other in dots:
                if other != option[0]:
                    additions.add(tuple(sorted((option[0], other))))

    low_degree = [
        vertex
        for vertex in range(n * n)
        if bits & (1 << vertex) and u_degree(bits, n, vertex) <= 2
    ]
    removals = list(combinations(low_degree, 2))
    best = baseline
    if not args.skip_exchange:
        checked = 0
        for added in sorted(additions):
            with_additions = bits
            for vertex in added:
                with_additions |= 1 << vertex
            for removed in removals:
                child = with_additions
                for vertex in removed:
                    child &= ~(1 << vertex)
                checked += 1
                metrics = dual_metrics(child, n)
                if metrics.score < best.score:
                    best = metrics
                    print(
                        f"improved checked={checked} add={added} remove={removed} "
                        f"score={metrics.score} edges={metrics.edge_count}"
                    )
                if metrics.components != 1:
                    continue
                rows = bits_to_rows(child, n)
                info = run_check(n, rows, verbose=True)
                if not info["all_ok"]:
                    raise AssertionError(
                        "connected exact-count exchange failed verification"
                    )
                print(
                    f"found checked={checked} add={added} remove={removed} "
                    f"cycle_excess={metrics.cycle_excess}"
                )
                print("\n".join(rows))
                return
        print(
            f"no two-for-two repair; checked={checked} additions={len(additions)} "
            f"removal_pairs={len(removals)} best={best.score}"
        )

    height = args.patch_height
    width = args.patch_width
    patch = [
        row * n + column
        for row in range(n - height, n)
        for column in range(width)
    ]
    patch_mask = sum(1 << vertex for vertex in patch)
    outside = bits & ~patch_mask
    patch_count = (bits & patch_mask).bit_count()

    total_faces = (n - 1) ** 2 + 1
    parent = list(range(total_faces))

    def find(value: int) -> int:
        while parent[value] != value:
            parent[value] = parent[parent[value]]
            value = parent[value]
        return value

    def union(left: int, right: int) -> None:
        left, right = find(left), find(right)
        if left != right:
            parent[right] = left

    def face(row: int, column: int) -> int:
        return 1 + row * (n - 1) + column

    dynamic_edges = []
    for row in range(n):
        for column in range(n - 1):
            vertices = (row * n + column, row * n + column + 1)
            dual = (
                0 if row == 0 else face(row - 1, column),
                0 if row + 1 == n else face(row, column),
            )
            if any(patch_mask & (1 << vertex) for vertex in vertices):
                dynamic_edges.append((*vertices, *dual))
            elif all(outside & (1 << vertex) for vertex in vertices):
                union(*dual)
    for row in range(n - 1):
        for column in range(n):
            vertices = (row * n + column, (row + 1) * n + column)
            dual = (
                0 if column == 0 else face(row, column - 1),
                0 if column + 1 == n else face(row, column),
            )
            if any(patch_mask & (1 << vertex) for vertex in vertices):
                dynamic_edges.append((*vertices, *dual))
            elif all(outside & (1 << vertex) for vertex in vertices):
                union(*dual)

    roots = sorted({find(value) for value in range(total_faces)})
    root_ids = {root: index for index, root in enumerate(roots)}
    dynamic_edges = [
        (a, b, root_ids[find(left)], root_ids[find(right)])
        for a, b, left, right in dynamic_edges
    ]

    def patch_connects(child: int) -> bool:
        local_parent = list(range(len(roots)))

        def local_find(value: int) -> int:
            while local_parent[value] != value:
                local_parent[value] = local_parent[local_parent[value]]
                value = local_parent[value]
            return value

        components = len(roots)
        for a, b, left, right in dynamic_edges:
            if not child & (1 << a) or not child & (1 << b):
                continue
            left, right = local_find(left), local_find(right)
            if left != right:
                local_parent[right] = left
                components -= 1
        return components == 1

    print(
        f"{height}x{width} contracted search: static_components={len(roots)} "
        f"dynamic_edges={len(dynamic_edges)}"
    )
    checked = 0
    for selected in combinations(patch, patch_count):
        child = outside
        for vertex in selected:
            child |= 1 << vertex
        checked += 1
        if not patch_connects(child):
            continue
        rows = bits_to_rows(child, n)
        info = run_check(n, rows, verbose=True)
        if not info["all_ok"]:
            raise AssertionError("connected exact-count patch failed verification")
        print(
            f"found {height}x{width} patch checked={checked}"
        )
        print("\n".join(rows))
        return
    print(
        f"no {height}x{width} patch repair; checked={checked} "
        f"patch_count={patch_count}"
    )
    raise SystemExit(1)


if __name__ == "__main__":
    main()
