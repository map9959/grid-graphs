#!/usr/bin/env python3
"""Constrained local search around the residue-2 skeleton's bridge layer.

Fixes the skeleton's outer scaffold (top sandwich, regular stripe rows,
col n-2 anchor, bottom sandwich) and enumerates all configurations of the
"free" cells in rows 2 and 3 — the F-column cells (cols 0, 3, 6, …, 3(k-1))
plus the right-boundary col n-1 — that hit the target U-count `q(n)` and
satisfy `construction_lab.run_check`.

The search is exhaustive over the bridge-layer free cells: 2(k+1) cells with
a count constraint reduces the search space to C(2(k+1), m) where m is the
number of free Us required (typically very small).

Usage:
    python3 -m analysis.searches.search_skeleton_patch 11
    python3 -m analysis.searches.search_skeleton_patch 14 --extend  # also vary rows n-4, n-3
"""

from __future__ import annotations

import argparse
import itertools


from analysis.patterns.construction_lab import q_formula, run_check


def build_skeleton_scaffold(n: int) -> tuple[list[list[str]], list[tuple[int, int]]]:
    """Return (rows-as-mutable-cell-lists, free_cell_positions).

    The returned rows have stripe cells filled in for every middle row and the
    top/bottom sandwich rows fully populated. Cells listed in `free_cell_positions`
    are pre-set to "." and are the search variables.
    """
    if n % 3 != 2 or n < 5:
        raise ValueError("n must be 3k+2 with k>=1")
    k = (n - 2) // 3
    rows = [["." for _ in range(n)] for _ in range(n)]
    # Top sandwich.
    rows[0][1] = "U"
    for c in range(1, n):
        rows[1][c] = "U"
    # Bottom sandwich.
    for c in range(1, n - 1):
        rows[n - 2][c] = "U"
    rows[n - 1][1] = "U"
    rows[n - 1][n - 2] = "U"
    # Stripe + col n-2 anchor for middle rows (rows 2..n-3).
    for r in range(2, n - 2):
        for t in range(k):
            rows[r][3 * t + 1] = "U"
            rows[r][3 * t + 2] = "U"
        rows[r][n - 2] = "U"
    # Free cells: F-columns in rows 2 and 3, plus col n-1 (right boundary) at
    # rows 2, 3.
    f_cols = [3 * t for t in range(k)] + [n - 1]
    free = []
    for r in (2, 3):
        for c in f_cols:
            free.append((r, c))
    return rows, free


def build_extended_scaffold(n: int) -> tuple[list[list[str]], list[tuple[int, int]]]:
    """Same as build_skeleton_scaffold but also exposes rows n-4, n-3 as variable.

    For larger k where savings might be split across the top and bottom bridge
    layers (mirroring the n=14 witness's row-9/10 transition rows).
    """
    rows, free = build_skeleton_scaffold(n)
    k = (n - 2) // 3
    f_cols = [3 * t for t in range(k)] + [n - 1]
    for r in (n - 4, n - 3):
        for c in f_cols:
            free.append((r, c))
    return rows, free


def render(rows: list[list[str]]) -> list[str]:
    return ["".join(row) for row in rows]


def search(n: int, extend: bool = False, verbose: bool = False) -> list[list[str]]:
    if extend:
        rows, free = build_extended_scaffold(n)
    else:
        rows, free = build_skeleton_scaffold(n)
    target = q_formula(n)
    fixed_u = sum(row.count("U") for row in rows)
    free_u_count = target - fixed_u
    if free_u_count < 0 or free_u_count > len(free):
        print(f"n={n}: infeasible — fixed_u={fixed_u}, target={target}, "
              f"free={len(free)}")
        return []
    print(f"n={n}: fixed_u={fixed_u}, target={target}, free_cells={len(free)}, "
          f"need {free_u_count} Us in free cells")
    print(f"  free positions: {free}")
    n_combos = sum(1 for _ in itertools.combinations(free, free_u_count))
    print(f"  combinations to try: {n_combos}")
    print()
    valid = []
    tried = 0
    for combo in itertools.combinations(free, free_u_count):
        # Apply combo
        for r, c in combo:
            rows[r][c] = "U"
        # Check
        candidate = render(rows)
        info = run_check(n, candidate, verbose=False)
        tried += 1
        if info["all_ok"]:
            valid.append((combo, candidate))
            print(f"  VALID: {combo}")
            for line in candidate:
                print(f"    {line}")
            print()
        elif verbose:
            print(f"  combo {combo}: u_match={info['u_match']} "
                  f"dual={info['dual_connected']}/{info['dual_total']} "
                  f"forest={info['forest_ok']} ({info['forest_reason']})")
        # Undo
        for r, c in combo:
            rows[r][c] = "."
    print(f"\nTried {tried}, valid: {len(valid)}")
    return valid


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("n", type=int)
    parser.add_argument("--extend", action="store_true",
                        help="also vary rows n-4, n-3 (bottom bridge layer)")
    parser.add_argument("--verbose", action="store_true")
    args = parser.parse_args()
    search(args.n, extend=args.extend, verbose=args.verbose)


if __name__ == "__main__":
    main()
