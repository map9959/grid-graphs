#!/usr/bin/env python3
"""Construct and inspect the valid crossed-crop residue-two near-family."""

from __future__ import annotations

import argparse

from analysis.patterns.construction_lab import q_formula, run_check
from analysis.patterns.diagonal_patterns import residue_zero_phase_pattern
from analysis.searches.search_residue_anneal import dual_metrics, rows_to_bits


def delete_row_column(rows: list[str], deleted_row: int, deleted_column: int) -> list[str]:
    return [
        row[:deleted_column] + row[deleted_column + 1 :]
        for index, row in enumerate(rows)
        if index != deleted_row
    ]


def residue_two_phase_crop_pattern(n: int, crossed: bool = True) -> list[str]:
    """Return the valid n=3k+2 phase crop, optionally with crossed deletions."""
    if n % 3 != 2 or n < 23:
        raise ValueError("phase crop requires n = 3k+2 with k >= 7")
    k = (n - 2) // 3
    rows = [list(row) for row in delete_row_column(
        residue_zero_phase_pattern(n + 1), deleted_row=3, deleted_column=3
    )]
    if crossed:
        starts = [
            *range(3, 2 * k - 9, 4),
            *range(2 * k - 2, 3 * k - 3, 4),
        ]
        for row in starts:
            rows[row][2] = "."
            rows[row + 2][3] = "."
    return ["".join(row) for row in rows]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("n", type=int, nargs="?", default=23)
    parser.add_argument("--uncrossed", action="store_true")
    parser.add_argument("--print-grid", action="store_true")
    args = parser.parse_args()
    rows = residue_two_phase_crop_pattern(args.n, crossed=not args.uncrossed)
    info = run_check(args.n, rows, verbose=True)
    metrics = dual_metrics(rows_to_bits(rows), args.n)
    count = sum(row.count("U") for row in rows)
    print(
        f"count={count} target={q_formula(args.n)} excess={count-q_formula(args.n)} "
        f"dual_edges={metrics.edge_count} cycle_excess={metrics.cycle_excess}"
    )
    if not info["dual_ok"] or not info["forest_ok"]:
        raise SystemExit(1)
    if args.print_grid:
        print("\n".join(rows))


if __name__ == "__main__":
    main()
