#!/usr/bin/env python3
"""Display U-patterns in 3x3 block coordinates.

The diagonal proof seems to be organized by 3-row and 3-column strips. This
script takes a cached U-pattern and prints each 3-row band, split into 3-column
blocks, together with per-block counts.
"""

from __future__ import annotations

import argparse
import sys

from analysis.patterns.dual_decycling import parse_pattern


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.parse_args()
    rows = parse_pattern(sys.stdin.read())
    n = len(rows)
    print(f"n={n}")
    for br in range((n + 2) // 3):
        r0 = 3 * br
        band = rows[r0 : min(n, r0 + 3)]
        print(f"band {br} rows {r0}..{r0 + len(band) - 1}")
        for row in band:
            chunks = [row[c : min(n, c + 3)] for c in range(0, n, 3)]
            print("  " + " ".join(f"{chunk:<3}" for chunk in chunks))
        counts = []
        for bc, c0 in enumerate(range(0, n, 3)):
            cnt = 0
            for row in band:
                cnt += row[c0 : min(n, c0 + 3)].count("U")
            counts.append(f"{bc}:{cnt}")
        print("  block counts " + " ".join(counts))


if __name__ == "__main__":
    main()
