#!/usr/bin/env python3
"""Executable algebra certificate for the affine residue-two word family."""

from __future__ import annotations

import argparse

from analysis.patterns.construction_lab import dual_connectivity_check, forest_completion_check
from analysis.patterns.diagonal_patterns import _RESIDUE_TWO_AFFINE_17, residue_two_affine_pattern


def require(condition: bool, message: object) -> None:
    if not condition:
        raise ValueError(message)


def source_codes(k: int) -> tuple[list[int], list[int]]:
    if k < 5:
        raise ValueError("the affine family starts at k=5")
    repeated = k - 4
    rows = [*range(9), *([9, 10, 11] * repeated), *range(12, 17)]
    columns = [*range(4), *([4, 5, 6] * repeated), *range(7, 17)]
    return rows, columns


def closed_form_pattern(k: int) -> list[str]:
    row_codes, column_codes = source_codes(k)
    return [
        "".join(_RESIDUE_TWO_AFFINE_17[r][c] for c in column_codes)
        for r in row_codes
    ]


def induced_edge_count(rows: list[str]) -> int:
    horizontal = sum(
        row[c] == row[c + 1] == "U"
        for row in rows
        for c in range(len(row) - 1)
    )
    vertical = sum(
        rows[r][c] == rows[r + 1][c] == "U"
        for r in range(len(rows) - 1)
        for c in range(len(rows))
    )
    return horizontal + vertical


def check(k: int, topology: bool) -> None:
    n = 3 * k + 2
    rows = closed_form_pattern(k)
    require(len(rows) == n and all(len(row) == n for row in rows), (k, "shape"))
    require(rows == residue_two_affine_pattern(n), (k, "closed form differs from pump"))

    actual_u = sum(row.count("U") for row in rows)
    expected_u = 6 * k * k + 6 * k - 1
    require(actual_u == expected_u, (k, actual_u, expected_u))

    actual_edges = induced_edge_count(rows)
    expected_edges = 9 * k * k + 8 * k - 8
    require(actual_edges == expected_edges, (k, actual_edges, expected_edges))

    vertices = 1 + (n - 1) ** 2
    require(actual_edges - vertices + 1 == 2 * k - 9, (k, "edge surplus"))

    if topology:
        dual_ok, connected, total = dual_connectivity_check(rows)
        forest_ok, reason = forest_completion_check(rows)
        require(dual_ok, (k, connected, total))
        require(forest_ok, (k, reason))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-k", type=int, default=39)
    parser.add_argument(
        "--algebra-only",
        action="store_true",
        help="skip dual-connectivity and forced-forest checks",
    )
    args = parser.parse_args()
    if args.max_k < 5:
        parser.error("--max-k must be at least 5")
    for k in range(5, args.max_k + 1):
        check(k, not args.algebra_only)
    mode = "algebra" if args.algebra_only else "algebra and topology"
    print(f"checked affine {mode} for k=5..{args.max_k} (n<= {3 * args.max_k + 2})")


if __name__ == "__main__":
    main()
