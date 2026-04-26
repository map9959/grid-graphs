#!/usr/bin/env python3
"""Catalog 3x3 U-tiles appearing in cached diagonal witnesses."""

from __future__ import annotations

import argparse
import sys
from collections import Counter, defaultdict

from dual_decycling import parse_pattern


def tile_key(rows: list[str], r0: int, c0: int) -> tuple[str, ...]:
    n = len(rows)
    return tuple(row[c0 : min(n, c0 + 3)].ljust(3, " ") for row in rows[r0 : min(n, r0 + 3)])


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.parse_args()
    rows = parse_pattern(sys.stdin.read())
    n = len(rows)
    counts: Counter[tuple[str, ...]] = Counter()
    positions: dict[tuple[str, ...], list[tuple[int, int]]] = defaultdict(list)
    for r0 in range(0, n, 3):
        for c0 in range(0, n, 3):
            key = tile_key(rows, r0, c0)
            counts[key] += 1
            positions[key].append((r0 // 3, c0 // 3))
    print(f"n={n} distinct_tiles={len(counts)}")
    labels = {key: chr(ord("A") + i) for i, (key, _cnt) in enumerate(counts.most_common())}
    print("tile matrix:")
    for r0 in range(0, n, 3):
        row = []
        for c0 in range(0, n, 3):
            row.append(labels[tile_key(rows, r0, c0)])
        print("  " + " ".join(row))
    print("tile definitions:")
    for key, cnt in counts.most_common():
        ucnt = sum(row.count("U") for row in key)
        print(f"{labels[key]}: count={cnt} U={ucnt} positions={positions[key]}")
        for row in key:
            print("  " + row)


if __name__ == "__main__":
    main()
