#!/usr/bin/env python3
"""Greedy/structured search for residue-0 and residue-2 U-patterns.

Starts from a candidate baseline (v5 stripes plus optional perturbations) and
performs local moves that preserve dual connectivity and forest condition while
reducing |U| toward the conjectured q(n).

This is exploratory tooling; the eventual goal is to find a clean parametric
pattern by hand-inspecting the search outputs.
"""

from __future__ import annotations

import argparse
import random
from itertools import combinations
from typing import Callable

from analysis.patterns.construction_lab import (
    DSU,
    dual_connectivity_check,
    forest_completion_check,
    q_formula,
    run_check,
)


def make_stripes(n: int) -> list[str]:
    """Pure column stripes: rows are `.UU.UU.UU...` for n divisible by 3."""
    k = n // 3
    out = []
    for _ in range(n):
        line = []
        for t in range(k):
            line.append(".")
            line.append("U")
            line.append("U")
        out.append("".join(line))
    return out


def make_stripes_residue2(n: int) -> list[str]:
    """For n = 3k+2: stripes with two extra rightmost columns of U.

    Each row is `.UU.UU....UU UU` (the trailing two columns also U).
    """
    k = (n - 2) // 3
    out = []
    for _ in range(n):
        line = []
        for t in range(k):
            line.append(".")
            line.append("U")
            line.append("U")
        line.append("U")
        line.append("U")
        out.append("".join(line))
    return out


def remove_cells(rows: list[str], removals: set[tuple[int, int]]) -> list[str]:
    out = []
    for r, row in enumerate(rows):
        cells = list(row)
        for rr, c in removals:
            if rr == r and 0 <= c < len(cells):
                cells[c] = "."
        out.append("".join(cells))
    return out


def add_cells(rows: list[str], additions: set[tuple[int, int]]) -> list[str]:
    out = []
    for r, row in enumerate(rows):
        cells = list(row)
        for rr, c in additions:
            if rr == r and 0 <= c < len(cells):
                cells[c] = "U"
        out.append("".join(cells))
    return out


def candidate_check(rows: list[str]) -> bool:
    d_ok, _, _ = dual_connectivity_check(rows)
    if not d_ok:
        return False
    f_ok, _ = forest_completion_check(rows)
    return f_ok


def random_local_search(
    n: int,
    seed: int,
    initial: list[str],
    target: int,
    steps: int = 5000,
    verbose: bool = False,
) -> list[str] | None:
    """Try to reach |U|=target by random U toggles preserving validity."""
    rng = random.Random(seed)
    rows = list(initial)
    cur_u = sum(r.count("U") for r in rows)
    for step in range(steps):
        if cur_u == target and candidate_check(rows):
            return rows
        # Pick a random cell to toggle.
        r = rng.randrange(n)
        c = rng.randrange(n)
        cells = list(rows[r])
        if cells[c] == "U":
            new = "."
        else:
            new = "U"
        cells[c] = new
        new_rows = list(rows)
        new_rows[r] = "".join(cells)
        new_u = sum(row.count("U") for row in new_rows)
        # Accept only if move is toward target and valid.
        if abs(new_u - target) > abs(cur_u - target):
            continue
        if not candidate_check(new_rows):
            continue
        rows = new_rows
        cur_u = new_u
        if verbose and step % 100 == 0:
            print(f"step={step} |U|={cur_u} target={target}")
    return None


def constrained_search(
    n: int,
    initial: list[str],
    target: int,
    allowed_removal_cells: list[tuple[int, int]],
    chunk_sizes: list[int] | None = None,
) -> list[str] | None:
    """Try to remove `|U(initial)| - target` cells from a restricted candidate
    set, using exhaustive small-batch combinatorial search."""
    cur_u = sum(r.count("U") for r in initial)
    n_remove = cur_u - target
    if chunk_sizes is None:
        chunk_sizes = [1, 2, 3, 4]
    rows = list(initial)
    remaining = list(allowed_removal_cells)
    while n_remove > 0:
        progressed = False
        for k in chunk_sizes:
            if k > n_remove:
                break
            best = None
            for combo in combinations(remaining, k):
                test = remove_cells(rows, set(combo))
                if candidate_check(test):
                    best = combo
                    break
            if best is not None:
                rows = remove_cells(rows, set(best))
                for cell in best:
                    if cell in remaining:
                        remaining.remove(cell)
                n_remove -= k
                progressed = True
                break
        if not progressed:
            return None
    return rows


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("n", type=int)
    parser.add_argument("--mode", choices=["random", "constrained"], default="constrained")
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--steps", type=int, default=5000)
    args = parser.parse_args()
    n = args.n
    target = q_formula(n)
    if n % 3 == 0:
        initial = make_stripes(n)
    elif n % 3 == 2:
        initial = make_stripes_residue2(n)
    else:
        raise SystemExit("unsupported residue")
    print(f"initial |U| = {sum(r.count('U') for r in initial)}, target = {target}")
    if args.mode == "random":
        out = random_local_search(n, args.seed, initial, target, steps=args.steps, verbose=True)
    else:
        # Allow removals on the rightmost column and on the first row.
        cells = [(r, n - 1) for r in range(n)] + [(0, c) for c in range(n)]
        cells = list(set(cells))
        out = constrained_search(n, initial, target, cells)
    if out is None:
        print("no construction found")
    else:
        info = run_check(n, out, verbose=True)
        for row in out:
            print(row)


if __name__ == "__main__":
    main()
