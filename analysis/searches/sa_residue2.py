#!/usr/bin/env python3
"""SA search for residue-2 q-witnesses.

Implements simulated annealing starting from various seed patterns to find
valid q-constructions for residue 2 (n = 3k+2). Used to populate cached
witnesses when no parametric form is available.

Seeds tried (in order of preference):
  1. Cached residue_two_explicit_pattern(n_smaller) padded with random slab.
  2. v35 (residue-1 at n_prime=n+2 restricted to n×n).
  3. Random pattern with target U count.

The SA toggles 2-6 cells at a time, accepting moves that maintain validity
and reduce |U|−target| (with Metropolis criterion at temperature T).
"""

from __future__ import annotations

import argparse
import math
import random
import sys
import time

from analysis.patterns.construction_lab import (
    dual_connectivity_check,
    forest_completion_check,
    q_formula,
)
from analysis.patterns.diagonal_patterns import (
    residue_one_pattern,
    residue_two_explicit_pattern,
)


def is_valid(rows: list[str]) -> bool:
    d_ok, _, _ = dual_connectivity_check(rows)
    if not d_ok:
        return False
    f_ok, _ = forest_completion_check(rows)
    return f_ok


def variant_v35_grid(n: int) -> list[list[bool]]:
    """Residue-1 at n_prime = n+2, restricted to top-left n×n."""
    n_prime = n + 2
    res1 = residue_one_pattern(n_prime)
    u = [[False] * n for _ in range(n)]
    for r in range(n):
        for c in range(n):
            if res1[r][c] == "U":
                u[r][c] = True
    return u


def slab_seed_grid(n: int, n_smaller: int, density: float, rng: random.Random) -> list[list[bool]]:
    """Embed cached pattern at n_smaller, fill slab area randomly with given density."""
    pattern = residue_two_explicit_pattern(n_smaller)
    n_diff = n - n_smaller
    ir = rng.randint(1, n_smaller - 2)
    ic = rng.randint(1, n_smaller - 2)
    grid = [[False] * n for _ in range(n)]

    def map_r(r):
        return r if r <= ir else r + n_diff

    def map_c(c):
        return c if c <= ic else c + n_diff

    for r in range(n_smaller):
        for c in range(n_smaller):
            if pattern[r][c] == "U":
                grid[map_r(r)][map_c(c)] = True
    # Fill slab rows
    for i in range(n_diff):
        nr = ir + 1 + i
        for c in range(n):
            if rng.random() < density:
                grid[nr][c] = True
    # Fill slab cols
    for i in range(n_diff):
        nc = ic + 1 + i
        for r in range(n):
            if rng.random() < density:
                grid[r][nc] = True
    return grid


def sa_run(
    n: int, target: int, initial_grid: list[list[bool]], time_limit: float, seed: int
) -> tuple[int, list[list[bool]], int]:
    rng = random.Random(seed)
    grid = [row[:] for row in initial_grid]
    rows = ["".join("U" if x else "." for x in row) for row in grid]
    cur_count = sum(r.count("U") for r in rows)
    best_count = cur_count
    best_grid = [row[:] for row in grid]

    start = time.time()
    iters = 0
    while time.time() - start < time_limit and cur_count != target:
        iters += 1
        T = max(0.02, 2.0 * math.exp(-iters / 10000))
        n_toggle = rng.randint(2, 6)
        cells = list(
            set([(rng.randrange(n), rng.randrange(n)) for _ in range(n_toggle)])
        )
        olds = [grid[r][c] for r, c in cells]
        for (r, c), old in zip(cells, olds):
            grid[r][c] = not old
        rows = ["".join("U" if x else "." for x in row) for row in grid]
        new_count = sum(r.count("U") for r in rows)
        if not is_valid(rows):
            for (r, c), old in zip(cells, olds):
                grid[r][c] = old
            continue
        # Prefer staying close to target. Penalize undershoot more (since we want q-construction).
        cur_dist = abs(cur_count - target)
        new_dist = abs(new_count - target)
        # Add penalty for undershoot (count < target)
        if new_count < target:
            new_dist += 5  # extra penalty
        if cur_count < target:
            cur_dist += 5
        delta = new_dist - cur_dist
        if delta < 0 or rng.random() < math.exp(-delta / T):
            cur_count = new_count
            if abs(cur_count - target) < abs(best_count - target):
                best_count = cur_count
                best_grid = [row[:] for row in grid]
        else:
            for (r, c), old in zip(cells, olds):
                grid[r][c] = old
    if cur_count != target and abs(best_count - target) < abs(cur_count - target):
        return best_count, best_grid, iters
    return cur_count, grid, iters


def find_residue_two(n: int, time_budget: float = 60.0) -> list[str] | None:
    """Find a valid q-construction for residue-2 n via SA. Returns rows or None."""
    target = q_formula(n)
    best_count = float("inf")
    best_grid = None

    # Try cached if exists
    try:
        rows = residue_two_explicit_pattern(n)
        if sum(r.count("U") for r in rows) == target and is_valid(rows):
            return rows
    except KeyError:
        pass

    # Determine smaller cached size
    smaller = None
    for ns in [14, 11, 8, 5]:
        if ns < n:
            smaller = ns
            break

    # SA seeds
    start = time.time()
    seed_idx = 0
    while time.time() - start < time_budget:
        seed_idx += 1
        rng = random.Random(seed_idx * 17)
        # Choose initial grid
        if smaller is not None and rng.random() < 0.7:
            density = 0.4 + rng.random() * 0.4  # 0.4-0.8
            initial = slab_seed_grid(n, smaller, density, rng)
        else:
            initial = variant_v35_grid(n)

        time_per_run = min(15.0, time_budget - (time.time() - start))
        if time_per_run < 1:
            break
        cur_count, grid, iters = sa_run(n, target, initial, time_per_run, seed_idx)
        if cur_count < best_count:
            best_count = cur_count
            best_grid = [r[:] for r in grid]
            print(f"  seed {seed_idx}: {best_count} (target {target})", file=sys.stderr)
            if cur_count == target:
                rows = ["".join("U" if x else "." for x in row) for row in grid]
                if is_valid(rows):
                    return rows

    if best_grid is None:
        return None
    rows = ["".join("U" if x else "." for x in row) for row in best_grid]
    if sum(r.count("U") for r in rows) == target and is_valid(rows):
        return rows
    return None


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("n", type=int)
    parser.add_argument("--time", type=float, default=60.0)
    args = parser.parse_args()
    if args.n % 3 != 2 or args.n < 5:
        raise SystemExit("n must be 3k+2 with k >= 1")
    target = q_formula(args.n)
    print(f"# n={args.n}  target_q={target}")
    rows = find_residue_two(args.n, time_budget=args.time)
    if rows is None:
        print(f"# FAILED to find q-witness within time budget", file=sys.stderr)
        return
    for row in rows:
        print(row)


if __name__ == "__main__":
    main()
