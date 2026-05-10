#!/usr/bin/env python3
"""Compare a cached U witness to the residue-matched skeleton pattern.

For n = 3k + 2 the reference is `residue_two_skeleton_pattern`.
For n = 3k     the reference is `residue_zero_skeleton_pattern`.
For n = 3k + 1 the reference is `residue_one_pattern`.

Output per cell: `+` (witness has U, skeleton does not),
`-` (skeleton has U, witness does not), `=` (both U), `.` (neither).
"""

from __future__ import annotations

import argparse

from diagonal_patterns import (
    q_formula,
    residue_one_pattern,
    residue_two_skeleton_pattern,
    residue_zero_skeleton_pattern,
)


def skeleton_for(n: int) -> list[str]:
    r = n % 3
    if r == 1:
        return residue_one_pattern(n)
    if r == 2:
        return residue_two_skeleton_pattern(n)
    return residue_zero_skeleton_pattern(n)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("n", type=int)
    parser.add_argument("--path", default=None,
                        help="witness file path (default data/diagonal_u_{n}.txt)")
    args = parser.parse_args()
    n = args.n
    path = args.path or f"data/diagonal_u_{n}.txt"
    actual = [line.strip() for line in open(path, encoding="utf-8") if line.strip()]
    if len(actual) != n:
        raise SystemExit(f"witness has {len(actual)} rows, expected {n}")
    skel = skeleton_for(n)

    plus = []  # witness has U, skeleton does not
    minus = []  # skeleton has U, witness does not
    same = 0
    for r in range(n):
        for c in range(n):
            a = actual[r][c] == "U"
            s = skel[r][c] == "U"
            if a and not s:
                plus.append((r, c))
            elif s and not a:
                minus.append((r, c))
            elif a and s:
                same += 1

    a_count = sum(row.count("U") for row in actual)
    s_count = sum(row.count("U") for row in skel)
    q = q_formula(n)
    print(f"n={n}  q(n)={q}  witness={a_count}  skeleton={s_count}  "
          f"skeleton_excess={s_count - q}")
    print(f"plus={len(plus)} minus={len(minus)} same={same}  "
          f"net={len(plus) - len(minus)}")
    print()

    print("side-by-side  (witness | skeleton | diff: + only-witness, - only-skeleton, = both, . neither)")
    for r in range(n):
        wrow = actual[r]
        srow = skel[r]
        diff = []
        for c in range(n):
            a = wrow[c] == "U"
            s = srow[c] == "U"
            if a and s:
                diff.append("=")
            elif a and not s:
                diff.append("+")
            elif s and not a:
                diff.append("-")
            else:
                diff.append(".")
        wcount = wrow.count("U")
        scount = srow.count("U")
        print(f"  r{r:>2}: {wrow}  |  {srow}  |  {''.join(diff)}  "
              f"(w={wcount} s={scount} d={wcount - scount:+d})")
    print()
    print("plus_by_row (cells where witness saves over the skeleton's gaps):")
    for r in range(n):
        cols = [c for rr, c in plus if rr == r]
        if cols:
            print(f"  r{r:>2}: {cols}")
    print("minus_by_row (cells the skeleton has but the witness drops):")
    for r in range(n):
        cols = [c for rr, c in minus if rr == r]
        if cols:
            print(f"  r{r:>2}: {cols}")


if __name__ == "__main__":
    main()
