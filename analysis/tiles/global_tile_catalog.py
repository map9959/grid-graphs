#!/usr/bin/env python3
"""Build a global 3x3 tile catalog across multiple U-pattern files."""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from pathlib import Path

from analysis.patterns.dual_decycling import parse_pattern


def tile_key(rows: list[str], r0: int, c0: int) -> tuple[str, ...]:
    n = len(rows)
    return tuple(row[c0 : min(n, c0 + 3)].ljust(3, " ") for row in rows[r0 : min(n, r0 + 3)])


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("files", nargs="+", type=Path)
    args = parser.parse_args()

    counts: Counter[tuple[str, ...]] = Counter()
    matrices: dict[str, list[list[tuple[str, ...]]]] = {}
    locs: dict[tuple[str, ...], list[str]] = defaultdict(list)
    for path in args.files:
        rows = parse_pattern(path.read_text())
        n = len(rows)
        mat = []
        for r0 in range(0, n, 3):
            row = []
            for c0 in range(0, n, 3):
                key = tile_key(rows, r0, c0)
                counts[key] += 1
                locs[key].append(f"{path.stem}@({r0//3},{c0//3})")
                row.append(key)
            mat.append(row)
        matrices[path.stem] = mat

    labels = {key: f"T{i}" for i, (key, _cnt) in enumerate(counts.most_common(), start=1)}
    for name, mat in matrices.items():
        print(f"{name}:")
        for row in mat:
            print("  " + " ".join(f"{labels[key]:>3}" for key in row))
    print("tiles:")
    for key, cnt in counts.most_common():
        print(f"{labels[key]} count={cnt} U={sum(row.count('U') for row in key)} locs={locs[key]}")
        for row in key:
            print("  " + row)


if __name__ == "__main__":
    main()
