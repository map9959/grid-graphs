#!/usr/bin/env python3
"""Compare cached U witnesses to cropped residue-1 constructions."""

from __future__ import annotations

import argparse

from diagonal_patterns import q_formula, residue_one_pattern


def source_residue_one(n: int) -> int:
    return n if n % 3 == 1 else n + ((1 - n) % 3)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("n", type=int)
    args = parser.parse_args()
    n = args.n
    src = source_residue_one(n)
    crop = [row[:n] for row in residue_one_pattern(src)[:n]]
    actual = [line.strip() for line in open(f"data/diagonal_u_{n}.txt", encoding="utf-8")]
    plus = []
    minus = []
    for r in range(n):
        for c in range(n):
            if actual[r][c] == "U" and crop[r][c] == ".":
                plus.append((r, c))
            if actual[r][c] == "." and crop[r][c] == "U":
                minus.append((r, c))
    print(f"n={n} source={src}")
    print(f"crop_count={sum(row.count('U') for row in crop)} actual={sum(row.count('U') for row in actual)} q={q_formula(n)}")
    print(f"plus={len(plus)} minus={len(minus)} net={len(plus)-len(minus)}")
    print("plus_by_row:")
    for r in range(n):
        cols = [c for rr, c in plus if rr == r]
        if cols:
            print(f"  {r}: {cols}")
    print("minus_by_row:")
    for r in range(n):
        cols = [c for rr, c in minus if rr == r]
        if cols:
            print(f"  {r}: {cols}")


if __name__ == "__main__":
    main()
