#!/usr/bin/env python3
"""Search exact-count rewrites around the residue-2 hand-derived slab.

Unlike `sa_residue2.py`, this search keeps the U count fixed and assigns a
graded penalty to disconnected dual faces and forced cycles. It can therefore
cross invalid intermediate states instead of requiring every move to preserve
validity.
"""

from __future__ import annotations

import argparse
import math
import random
import time

from analysis.patterns.construction_lab import (
    DSU,
    dual_connectivity_check,
    q_formula,
    run_check,
)
from analysis.patterns.diagonal_patterns import residue_two_explicit_pattern
from analysis.transport.slab_construction import slab_extend_general


def forced_cycle_count(rows: list[str]) -> int:
    n = len(rows)
    is_u = [ch == "U" for row in rows for ch in row]
    dsu = DSU(range(n * n))
    cycles = 0
    for r in range(n):
        for c in range(n):
            a = r * n + c
            if c + 1 < n:
                b = a + 1
                if not (is_u[a] and is_u[b]) and not dsu.union(a, b):
                    cycles += 1
            if r + 1 < n:
                b = a + n
                if not (is_u[a] and is_u[b]) and not dsu.union(a, b):
                    cycles += 1
    return cycles


def structural_penalty(rows: list[str]) -> tuple[int, int, int]:
    _, connected, total = dual_connectivity_check(rows)
    missing = total - connected
    cycles = forced_cycle_count(rows)
    return missing + cycles, missing, cycles


def slab_distance(index: int, start: int, width: int = 3) -> int:
    if start <= index < start + width:
        return -1
    if index < start:
        return start - index - 1
    return index - start - width


def mutable_cells(n: int, ir: int, ic: int, halo: int) -> list[tuple[int, int]]:
    if halo < 0:
        return [(r, c) for r in range(n) for c in range(n)]
    return [
        (r, c)
        for r in range(n)
        for c in range(n)
        if slab_distance(r, ir) < halo or slab_distance(c, ic) < halo
    ]


def render(grid: list[list[bool]]) -> list[str]:
    return ["".join("U" if value else "." for value in row) for row in grid]


def search(
    old_n: int,
    halo: int,
    time_limit: float,
    seed: int,
) -> tuple[list[str] | None, tuple[int, int, int], int]:
    old = residue_two_explicit_pattern(old_n)
    initial = slab_extend_general(old)
    n = old_n + 3
    target = q_formula(n)
    ir, ic = old_n - 2, old_n - 3
    mutable = mutable_cells(n, ir, ic, halo)
    rng = random.Random(seed)
    deadline = time.monotonic() + time_limit
    iterations = 0
    best_rows = initial
    best_score = structural_penalty(initial)

    while time.monotonic() < deadline:
        grid = [[value == "U" for value in row] for row in initial]
        excess = sum(sum(row) for row in grid) - target
        removable = [(r, c) for r, c in mutable if grid[r][c]]
        if excess < 0 or len(removable) < excess:
            raise ValueError("initial slab cannot reach target using mutable cells")
        for r, c in rng.sample(removable, excess):
            grid[r][c] = False

        rows = render(grid)
        score = structural_penalty(rows)
        restart_iterations = 0
        while time.monotonic() < deadline:
            iterations += 1
            restart_iterations += 1
            us = [(r, c) for r, c in mutable if grid[r][c]]
            dots = [(r, c) for r, c in mutable if not grid[r][c]]
            move_size = rng.randint(1, min(3, len(us), len(dots)))
            removes = rng.sample(us, move_size)
            adds = rng.sample(dots, move_size)
            for r, c in removes:
                grid[r][c] = False
            for r, c in adds:
                grid[r][c] = True
            candidate = render(grid)
            candidate_score = structural_penalty(candidate)

            if candidate_score < best_score:
                best_score = candidate_score
                best_rows = candidate
            if candidate_score[0] == 0:
                return candidate, candidate_score, iterations

            temperature = max(0.05, 2.0 * math.exp(-restart_iterations / 5000))
            delta = candidate_score[0] - score[0]
            if delta <= 0 or rng.random() < math.exp(-delta / temperature):
                rows = candidate
                score = candidate_score
            else:
                for r, c in removes:
                    grid[r][c] = True
                for r, c in adds:
                    grid[r][c] = False

            if restart_iterations >= 20000:
                break

    return None, best_score, iterations


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("old_n", type=int, choices=(8, 11, 14))
    parser.add_argument(
        "--halo",
        type=int,
        default=1,
        help="copied-cell layers mutable around the slab; -1 allows all cells",
    )
    parser.add_argument("--time", type=float, default=30.0)
    parser.add_argument("--seed", type=int, default=1)
    args = parser.parse_args()

    rows, score, iterations = search(args.old_n, args.halo, args.time, args.seed)
    print(f"iterations={iterations} best={score}")
    if rows is None:
        raise SystemExit(1)
    info = run_check(args.old_n + 3, rows, verbose=True)
    if not info["all_ok"]:
        raise SystemExit("zero structural penalty did not produce a valid witness")
    for row in rows:
        print(row)


if __name__ == "__main__":
    main()
