#!/usr/bin/env python3
"""Diagnose whether cached residue-2 witnesses differ by a bounded slab rewrite.

For every placement of three inserted rows and columns, this compares the
mapped old pattern with a cached larger pattern. Cells in the inserted cross
are free slab content; mismatches elsewhere are rewrites of copied old cells.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass

from analysis.patterns.diagonal_patterns import residue_two_explicit_pattern


def transpose(rows: list[str]) -> list[str]:
    return ["".join(row[c] for row in rows) for c in range(len(rows))]


def map_index(index: int, insertion: int, width: int) -> int:
    return index if index < insertion else index + width


def seam_distance(index: int, insertion: int) -> int:
    """Number of copied-cell layers between an old index and the seam."""
    return insertion - index - 1 if index < insertion else index - insertion


@dataclass(frozen=True)
class Alignment:
    ir: int
    ic: int
    slab_us: int
    removals: tuple[tuple[int, int], ...]
    additions: tuple[tuple[int, int], ...]
    halo_width: int

    @property
    def rewrites(self) -> int:
        return len(self.removals) + len(self.additions)

    @property
    def net_rewrite(self) -> int:
        return len(self.additions) - len(self.removals)


def analyze_alignment(
    old: list[str], new: list[str], ir: int, ic: int, width: int = 3
) -> Alignment:
    n_old = len(old)
    if len(new) != n_old + width:
        raise ValueError("new pattern size must equal old size plus slab width")

    slab_us = 0
    for r, row in enumerate(new):
        for c, value in enumerate(row):
            if value == "U" and (ir <= r < ir + width or ic <= c < ic + width):
                slab_us += 1

    removals = []
    additions = []
    max_distance = -1
    for r in range(n_old):
        nr = map_index(r, ir, width)
        for c in range(n_old):
            nc = map_index(c, ic, width)
            if old[r][c] == new[nr][nc]:
                continue
            if old[r][c] == "U":
                removals.append((r, c))
            else:
                additions.append((r, c))
            max_distance = max(
                max_distance,
                min(seam_distance(r, ir), seam_distance(c, ic)),
            )

    return Alignment(
        ir=ir,
        ic=ic,
        slab_us=slab_us,
        removals=tuple(removals),
        additions=tuple(additions),
        halo_width=max_distance + 1,
    )


def all_alignments(old: list[str], new: list[str]) -> list[Alignment]:
    n_old = len(old)
    return [
        analyze_alignment(old, new, ir, ic)
        for ir in range(n_old + 1)
        for ic in range(n_old + 1)
    ]


def print_best(old_n: int, new_n: int, use_transpose: bool, limit: int) -> None:
    old = residue_two_explicit_pattern(old_n)
    new = residue_two_explicit_pattern(new_n)
    if use_transpose:
        old = transpose(old)
        new = transpose(new)

    ranked = sorted(
        all_alignments(old, new),
        key=lambda a: (a.rewrites, a.halo_width, abs(a.net_rewrite), a.ir, a.ic),
    )
    orientation = "transpose" if use_transpose else "original"
    print(f"{old_n}->{new_n} ({orientation})")
    print("ir ic rewrites remove add slab_U net halo")
    for item in ranked[:limit]:
        print(
            f"{item.ir:2} {item.ic:2} {item.rewrites:8} "
            f"{len(item.removals):6} {len(item.additions):3} "
            f"{item.slab_us:6} {item.net_rewrite:3} {item.halo_width:4}"
        )
    best = ranked[0]
    print(f"best removals: {best.removals}")
    print(f"best additions: {best.additions}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("old_n", type=int, choices=(5, 8, 11))
    parser.add_argument("--transpose", action="store_true")
    parser.add_argument("--limit", type=int, default=8)
    args = parser.parse_args()
    print_best(args.old_n, args.old_n + 3, args.transpose, args.limit)


if __name__ == "__main__":
    main()
