#!/usr/bin/env python3
"""Compact statistics for U/non-full patterns.

Input is `grid_graphs fullub-pattern M N` output or a raw U-pattern block.
The script prints row run-lengths and modulo-3 column classes, which are useful
for detecting strip motifs in the diagonal construction.
"""

from __future__ import annotations

import argparse
import sys
from collections import Counter

from analysis.patterns.dual_decycling import parse_pattern, q_formula


def runs(row: str) -> str:
    out: list[str] = []
    i = 0
    while i < len(row):
        j = i + 1
        while j < len(row) and row[j] == row[i]:
            j += 1
        out.append(f"{row[i]}{j - i}")
        i = j
    return " ".join(out)


def mod_classes(row: str) -> str:
    cnt = Counter(i % 3 for i, ch in enumerate(row) if ch == "U")
    return "(" + ",".join(str(cnt[i]) for i in range(3)) + ")"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.parse_args()
    rows = parse_pattern(sys.stdin.read())
    n = len(rows)
    total = sum(row.count("U") for row in rows)
    print(f"n={n} |U|={total} q={q_formula(n)}")
    print("row  count  mod3      runs")
    for i, row in enumerate(rows):
        print(f"{i:>3}  {row.count('U'):>5}  {mod_classes(row):<9} {runs(row)}")
    print("strip3 totals:")
    for s in range((n + 2) // 3):
        block = rows[3 * s : min(n, 3 * s + 3)]
        print(f"{s:>3}: {sum(row.count('U') for row in block)}")
    print("sliding3 totals:")
    vals = [sum(rows[r + i].count("U") for i in range(3)) for r in range(max(0, n - 2))]
    print("  " + ",".join(map(str, vals)))


if __name__ == "__main__":
    main()
