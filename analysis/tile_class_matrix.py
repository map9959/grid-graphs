#!/usr/bin/env python3
"""Print 3x3 tile matrices reduced by dihedral symmetry classes."""

from __future__ import annotations

import argparse
import sys
from collections import Counter

from dual_decycling import parse_pattern
from tile_symmetry import canon


def tile_key(rows: list[str], r0: int, c0: int) -> tuple[str, ...] | None:
    n = len(rows)
    if r0 + 3 > n or c0 + 3 > n:
        return None
    return tuple(row[c0 : c0 + 3] for row in rows[r0 : r0 + 3])


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.parse_args()
    rows = parse_pattern(sys.stdin.read())
    n = len(rows)
    tiles = []
    for r0 in range(0, n - 2, 3):
        for c0 in range(0, n - 2, 3):
            key = tile_key(rows, r0, c0)
            if key is not None:
                tiles.append(canon(key))
    counts = Counter(tiles)
    labels = {key: f"C{i}" for i, (key, _cnt) in enumerate(counts.most_common(), start=1)}
    print(f"n={n}")
    for r0 in range(0, n - 2, 3):
        row = []
        for c0 in range(0, n - 2, 3):
            key = tile_key(rows, r0, c0)
            if key is not None:
                row.append(f"{labels[canon(key)]:>2}")
        print("  " + " ".join(row))
    print("classes:")
    for key, cnt in counts.most_common():
        print(f"{labels[key]} count={cnt} U={sum(row.count('U') for row in key)}")
        for row in key:
            print("  " + row)


if __name__ == "__main__":
    main()
