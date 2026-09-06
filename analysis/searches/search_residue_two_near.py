#!/usr/bin/env python3
"""Bounded repairs around reproducible residue-two n=17 near-hits."""

from __future__ import annotations

import argparse
from itertools import combinations

from analysis.patterns.construction_lab import run_check
from analysis.searches.search_residue_anneal import (
    bits_to_rows,
    bridge_additions,
    dual_metrics,
    rows_to_bits,
    u_degree,
)

NEAR_PHASECROP = [
    ".U.............UU",
    ".UUUUUUUUUUUUUUU.",
    ".UUU.UUUUU.UU.UU.",
    ".U.UUU...UUUU.UU.",
    ".UUUUUUUUUU.U.UU.",
    ".UU....UU.UUU.UU.",
    ".UUUUUUUUUUUUUUU.",
    ".UUUUU.........U.",
    ".U...UUUUUUUUUUU.",
    ".UUUUUUUUUUUUUUU.",
    ".UUUU..........U.",
    ".U..UUUUUUUUUUUU.",
    ".UUUUUUUUUUUUUUU.",
    ".UUU...........U.",
    ".U.UUUUUUUUUUUUU.",
    ".UUUUUUUUUUUUUUU.",
    ".UU..............",
]

NEAR_PUMP = [
    "..UU.............",
    ".UUUUUUUUUUUUUUUU",
    ".U..UUUUUUUUUUUU.",
    ".UUUU..........U.",
    ".UUUUUUUUUUUUUUU.",
    ".U...UUUUUUUUUUU.",
    ".UUUUU.........U.",
    ".UUUUUUUUUUUUUUU.",
    ".U....UUUUUUUUUU.",
    ".UUUUUU........U.",
    ".UUUUUUUUUUUUUUU.",
    ".U.....UU.UU.UUU.",
    ".UUUUUUUUUUUUU.U.",
    ".UU.UUU.....UUUU.",
    ".UUUU.UUUUUUU.UU.",
    "UUUUUUUUUUUUUUUUU",
    ".................",
]

NEAR_MACRO = [
    ".U...............",
    ".UUUUUUUUUUUUUUUU",
    ".UUUU.UU.UU.UU.UU",
    ".UU.UUUU.UU.UUUU.",
    ".UU.UU.U.UUUU.UU.",
    ".UU.UU.UUU.UU.UU.",
    ".UU.UU.UUU.UU.UU.",
    ".UU.UUUU.U.UU.UU.",
    ".UU.U.UUUU.UU.UU.",
    ".UUUU.U.UU.UU.UU.",
    ".U.UUUU.UU.UU.UU.",
    ".UUU.UU.UU.UU.UU.",
    ".UUU.UU.UU.UU.UU.",
    ".U...UU.UU.UU.UU.",
    ".UUUUUU.UU.UU.UU.",
    ".UUUUUUUUUUUUUUU.",
    ".U.............U.",
]


def search_two_exchange(bits: int, n: int) -> bool:
    baseline = dual_metrics(bits, n)
    dots = [vertex for vertex in range(n * n) if not bits & (1 << vertex)]
    additions = set()
    for option in bridge_additions(bits, n, baseline):
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
    checked = 0
    for added in sorted(additions):
        child = bits
        for vertex in added:
            child |= 1 << vertex
        for removed in removals:
            candidate = child
            for vertex in removed:
                candidate &= ~(1 << vertex)
            checked += 1
            if dual_metrics(candidate, n).components != 1:
                continue
            rows = bits_to_rows(candidate, n)
            if not run_check(n, rows, verbose=True)["all_ok"]:
                raise AssertionError("connected exchange failed verification")
            print(f"found two-for-two add={added} remove={removed}")
            print("\n".join(rows))
            return True
    print(
        f"no two-for-two repair; checked={checked} additions={len(additions)} "
        f"removal_pairs={len(removals)}"
    )
    return False


def search_patch(
    bits: int,
    n: int,
    row_start: int,
    column_start: int,
    height: int,
    width: int,
    two_corners: bool = False,
) -> bool:
    patch = {
        row * n + column
        for row in range(row_start, row_start + height)
        for column in range(column_start, column_start + width)
    }
    if two_corners:
        patch.update(
            row * n + column
            for row in range(height)
            for column in range(width)
        )
        patch.update(
            row * n + column
            for row in range(n - height, n)
            for column in range(n - width, n)
        )
    patch = sorted(patch)
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

    def connects(candidate: int) -> bool:
        local_parent = list(range(len(roots)))

        def local_find(value: int) -> int:
            while local_parent[value] != value:
                local_parent[value] = local_parent[local_parent[value]]
                value = local_parent[value]
            return value

        components = len(roots)
        for a, b, left, right in dynamic_edges:
            if not candidate & (1 << a) or not candidate & (1 << b):
                continue
            left, right = local_find(left), local_find(right)
            if left != right:
                local_parent[right] = left
                components -= 1
        return components == 1

    print(
        f"{height}x{width} {'two-corner' if two_corners else 'patch'} "
        f"at ({row_start},{column_start}): "
        f"count={patch_count} static_components={len(roots)} "
        f"dynamic_edges={len(dynamic_edges)}"
    )
    checked = 0
    for selected in combinations(patch, patch_count):
        candidate = outside
        for vertex in selected:
            candidate |= 1 << vertex
        checked += 1
        if not connects(candidate):
            continue
        rows = bits_to_rows(candidate, n)
        if not run_check(n, rows, verbose=True)["all_ok"]:
            raise AssertionError("connected patch failed verification")
        print(f"found patch after {checked} candidates")
        print("\n".join(rows))
        return True
    print(f"no patch repair; checked={checked}")
    return False


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--candidate", choices=("phasecrop", "pump", "macro"), default="phasecrop"
    )
    parser.add_argument("--patch-height", type=int, default=4)
    parser.add_argument("--patch-width", type=int, default=5)
    parser.add_argument("--skip-exchange", action="store_true")
    parser.add_argument("--two-corners", action="store_true")
    args = parser.parse_args()

    rows = {
        "phasecrop": NEAR_PHASECROP,
        "pump": NEAR_PUMP,
        "macro": NEAR_MACRO,
    }[args.candidate]
    n = len(rows)
    bits = rows_to_bits(rows)
    baseline = dual_metrics(bits, n)
    expected_score = (1, 1, 1) if args.candidate == "macro" else (1, 1, 0)
    if bits.bit_count() != 178 or baseline.score != expected_score:
        raise AssertionError(
            f"near-hit changed: count={bits.bit_count()} score={baseline.score}"
        )
    if not args.skip_exchange and search_two_exchange(bits, n):
        return

    if args.candidate == "phasecrop":
        row_start = n - args.patch_height
        column_start = n - args.patch_width
    elif args.candidate == "pump":
        row_start = 0
        column_start = 0
    else:
        row_start = 12 - args.patch_height // 2
        column_start = 3 - args.patch_width // 2
    if search_patch(
        bits,
        n,
        row_start,
        column_start,
        args.patch_height,
        args.patch_width,
        args.two_corners,
    ):
        return
    raise SystemExit(1)


if __name__ == "__main__":
    main()
