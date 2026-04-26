#!/usr/bin/env python3
"""Assemble U-patterns from a small 3x3 tile dictionary.

This is experimental tooling for the diagonal proof search. It makes it easy to
try tile matrices suggested by `tile_catalog.py` and pipe the resulting pattern
into `dual_decycling.py` or `u_pattern_stats.py`.
"""

from __future__ import annotations

import argparse
import sys


TILES = {
    # Common dense/cap/backbone tiles observed in witnesses.
    "A1": ["...", "UUU", "UUU"],
    "A2": [".UU", ".UU", ".UU"],
    "A3": ["UU.", "UU.", "UU."],
    "B1": [".U.", ".UU", ".UU"],
    "B2": [".U.", "UU.", "UU."],
    "C1": [".UU", "UUU", "..."],
    "C2": ["UU.", "UU.", ".UU"],
    "C3": ["UU.", ".UU", ".UU"],
    "D1": ["UUU", "U.U", "U.U"],
    "D2": ["UUU", "UU.", ".UU"],
    "E0": ["...", "...", "..."],
}


def assemble(matrix: list[list[str]]) -> list[str]:
    out: list[str] = []
    for row in matrix:
        block_rows = ["", "", ""]
        for label in row:
            tile = TILES[label]
            for i in range(3):
                block_rows[i] += tile[i]
        out.extend(block_rows)
    return out


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--trim", type=int, default=0, help="trim assembled square to n x n")
    args = parser.parse_args()
    matrix = [line.split() for line in sys.stdin.read().splitlines() if line.strip() and not line.startswith("#")]
    rows = assemble(matrix)
    if args.trim:
        rows = [row[: args.trim] for row in rows[: args.trim]]
    for row in rows:
        print(row)


if __name__ == "__main__":
    main()
