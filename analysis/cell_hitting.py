#!/usr/bin/env python3
"""Check the local 2x2 cell-hitting relaxation on n x n grids.

This solves the minimum-size set U such that every 2x2 cell has at least one
boundary U-U edge. It is a necessary condition for the forced-edge decycling
bound, but not sufficient. The output compares this local relaxation against
the conjectured non-full count q(n) = n^2 - P(n,n).
"""

from __future__ import annotations

import argparse
from functools import lru_cache
from math import inf


def q_formula(n: int) -> int:
    k, r = divmod(n, 3)
    if r == 0:
        return 6 * k * k - 3 * k + 2
    if r == 1:
        return 6 * k * k + k + 1
    return 6 * k * k + 5 * k + 3


@lru_cache(maxsize=None)
def valid_next_rows(n: int, prev: int) -> tuple[int, ...]:
    out: list[int] = []

    def rec(i: int, cur: int) -> None:
        if i == n:
            out.append(cur)
            return
        for bit in (0, 1):
            cur2 = cur | (bit << i)
            if i >= 1:
                j = i - 1
                hit = (
                    ((prev >> j) & 1 and (prev >> (j + 1)) & 1)
                    or ((cur2 >> j) & 1 and (cur2 >> (j + 1)) & 1)
                    or ((prev >> j) & 1 and (cur2 >> j) & 1)
                    or ((prev >> (j + 1)) & 1 and (cur2 >> (j + 1)) & 1)
                )
                if not hit:
                    continue
            rec(i + 1, cur2)

    rec(0, 0)
    return tuple(out)


def local_cell_hitting_min(n: int) -> int:
    pop = [mask.bit_count() for mask in range(1 << n)]
    dp = {mask: pop[mask] for mask in range(1 << n)}
    for _row in range(1, n):
        ndp: dict[int, int] = {}
        for prev, val in dp.items():
            for cur in valid_next_rows(n, prev):
                nv = val + pop[cur]
                if nv < ndp.get(cur, inf):
                    ndp[cur] = nv
        dp = ndp
    return min(dp.values())


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("nmax", type=int, nargs="?", default=15)
    args = parser.parse_args()
    print("n,local_min,conjectured_q,match")
    for n in range(4, args.nmax + 1):
        local = local_cell_hitting_min(n)
        q = q_formula(n)
        print(f"{n},{local},{q},{local == q}")


if __name__ == "__main__":
    main()
