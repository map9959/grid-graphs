#!/usr/bin/env python3
"""Group full 3x3 U-tiles up to dihedral symmetry."""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from pathlib import Path

from analysis.patterns.dual_decycling import parse_pattern


def tile_key(rows: list[str], r0: int, c0: int) -> tuple[str, ...] | None:
    n = len(rows)
    if r0 + 3 > n or c0 + 3 > n:
        return None
    return tuple(row[c0 : c0 + 3] for row in rows[r0 : r0 + 3])


def rot(tile: tuple[str, ...]) -> tuple[str, ...]:
    return tuple("".join(tile[2 - r][c] for r in range(3)) for c in range(3))


def refl(tile: tuple[str, ...]) -> tuple[str, ...]:
    return tuple(row[::-1] for row in tile)


def orbit(tile: tuple[str, ...]) -> list[tuple[str, ...]]:
    out = []
    t = tile
    for _ in range(4):
        out.append(t)
        out.append(refl(t))
        t = rot(t)
    return sorted(set(out))


def canon(tile: tuple[str, ...]) -> tuple[str, ...]:
    return orbit(tile)[0]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("files", nargs="+", type=Path)
    args = parser.parse_args()
    classes: Counter[tuple[str, ...]] = Counter()
    members: dict[tuple[str, ...], Counter[tuple[str, ...]]] = defaultdict(Counter)
    locs: dict[tuple[str, ...], list[str]] = defaultdict(list)
    for path in args.files:
        rows = parse_pattern(path.read_text())
        n = len(rows)
        for r0 in range(0, n - 2, 3):
            for c0 in range(0, n - 2, 3):
                tile = tile_key(rows, r0, c0)
                if tile is None:
                    continue
                c = canon(tile)
                classes[c] += 1
                members[c][tile] += 1
                locs[c].append(f"{path.stem}@({r0//3},{c0//3})")
    for i, (c, cnt) in enumerate(classes.most_common(), start=1):
        print(f"C{i} count={cnt} U={sum(row.count('U') for row in c)} locs={locs[c]}")
        print("canonical:")
        for row in c:
            print("  " + row)
        print("members:")
        for tile, tcnt in members[c].most_common():
            print(f"  x{tcnt}")
            for row in tile:
                print("    " + row)


if __name__ == "__main__":
    main()
