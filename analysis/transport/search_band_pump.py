#!/usr/bin/env python3
"""Search for residue-2 extensions obtained by pumping existing 3-cell bands.

The operation inserts a copy of three contiguous old row indices and three
contiguous old column indices. Every new cell is therefore inherited from the
old pattern, including the 3x3 intersection of the inserted bands.
"""

from __future__ import annotations

import argparse
import itertools
from dataclasses import dataclass

from analysis.patterns.construction_lab import q_formula, run_check
from analysis.patterns.diagonal_patterns import residue_two_explicit_pattern


@dataclass(frozen=True)
class Pump:
    row_insert: int
    row_source: int
    col_insert: int
    col_source: int


def pumped_indices(n: int, insertion: int, source: int) -> list[int]:
    if not 0 <= insertion <= n:
        raise ValueError("insertion must be between old indices")
    if not 0 <= source <= n - 3:
        raise ValueError("source must begin a contiguous old 3-band")
    return list(range(insertion)) + list(range(source, source + 3)) + list(range(insertion, n))


def pump_pattern(rows: list[str], pump: Pump) -> list[str]:
    n = len(rows)
    row_indices = pumped_indices(n, pump.row_insert, pump.row_source)
    col_indices = pumped_indices(n, pump.col_insert, pump.col_source)
    return ["".join(rows[r][c] for c in col_indices) for r in row_indices]


def every_face_has_dual_edge(rows: list[str]) -> bool:
    """Cheap necessary condition for dual connectivity."""
    n = len(rows)
    for r in range(n - 1):
        for c in range(n - 1):
            if not (
                (rows[r][c] == rows[r][c + 1] == "U")
                or (rows[r + 1][c] == rows[r + 1][c + 1] == "U")
                or (rows[r][c] == rows[r + 1][c] == "U")
                or (rows[r][c + 1] == rows[r + 1][c + 1] == "U")
            ):
                return False
    return True


def search(rows: list[str], limit: int | None = None) -> tuple[list[tuple[Pump, list[str]]], int]:
    n = len(rows)
    target = q_formula(n + 3)
    valid = []
    exact_count = 0
    for row_insert in range(n + 1):
        for row_source in range(n - 2):
            for col_insert in range(n + 1):
                for col_source in range(n - 2):
                    pump = Pump(row_insert, row_source, col_insert, col_source)
                    candidate = pump_pattern(rows, pump)
                    if sum(row.count("U") for row in candidate) != target:
                        continue
                    exact_count += 1
                    if run_check(n + 3, candidate)["all_ok"]:
                        valid.append((pump, candidate))
                        if limit is not None and len(valid) >= limit:
                            return valid, exact_count
    return valid, exact_count


def search_free_intersection(
    rows: list[str],
    limit: int | None = None,
    all_insertions: bool = False,
    all_sources: bool = False,
) -> tuple[list[tuple[Pump, list[str]]], int]:
    """Search tile-aligned pumps with an independently chosen 3x3 crossing."""
    n = len(rows)
    target = q_formula(n + 3)
    valid = []
    exact_count = 0
    insertions = list(range(n + 1)) if all_insertions else list(range(0, n - 1, 3))
    sources = list(range(n - 2)) if all_sources else list(range(0, n - 2, 3))
    intersection_offsets = list(itertools.product(range(3), repeat=2))
    for row_insert in insertions:
        for row_source in sources:
            for col_insert in insertions:
                for col_source in sources:
                    pump = Pump(row_insert, row_source, col_insert, col_source)
                    base = [list(row) for row in pump_pattern(rows, pump)]
                    for dr, dc in intersection_offsets:
                        base[row_insert + dr][col_insert + dc] = "."
                    base_count = sum(row.count("U") for row in base)
                    required = target - base_count
                    if not 0 <= required <= 9:
                        continue
                    for us in itertools.combinations(intersection_offsets, required):
                        exact_count += 1
                        for dr, dc in us:
                            base[row_insert + dr][col_insert + dc] = "U"
                        candidate = ["".join(row) for row in base]
                        if every_face_has_dual_edge(candidate) and run_check(n + 3, candidate)["all_ok"]:
                            valid.append((pump, candidate))
                            if limit is not None and len(valid) >= limit:
                                return valid, exact_count
                        for dr, dc in us:
                            base[row_insert + dr][col_insert + dc] = "."
    return valid, exact_count


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("old_n", type=int, choices=(5, 8, 11, 14))
    parser.add_argument("--limit", type=int, default=5)
    parser.add_argument("--free-intersection", action="store_true")
    parser.add_argument(
        "--all-insertions",
        action="store_true",
        help="allow non-tile-aligned insertion positions with aligned source bands",
    )
    parser.add_argument(
        "--all-sources",
        action="store_true",
        help="allow non-tile-aligned source bands",
    )
    args = parser.parse_args()
    rows = residue_two_explicit_pattern(args.old_n)
    if args.free_intersection:
        valid, exact_count = search_free_intersection(
            rows,
            limit=args.limit,
            all_insertions=args.all_insertions,
            all_sources=args.all_sources,
        )
    else:
        valid, exact_count = search(rows, limit=args.limit)
    print(f"exact-count candidates checked: {exact_count}")
    print(f"valid pumps found: {len(valid)}")
    for pump, candidate in valid:
        print(pump)
        for row in candidate:
            print(row)
        print()
    if not valid:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
