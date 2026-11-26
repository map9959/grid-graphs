#!/usr/bin/env python3
"""Generate a maximum-full-degree spanning tree of an n × n grid.

Run ``python3 generate_square_tree.py N`` for JSON with zero-based
[row, column] coordinates. Uses the proof's constructions, not a search.
"""

from __future__ import annotations

import argparse
import json
import sys
from collections.abc import Iterable

from analysis.patterns.diagonal_patterns import (
    residue_one_pattern,
    residue_two_pattern,
    residue_zero_pattern,
)


Vertex = tuple[int, int]
Edge = tuple[Vertex, Vertex]

# The cap words of GridGraphs/Constructions/CombWord.lean, one mask per column.
_COMB_LOOP = (
    0, 8, 3, 0, 12, 1, 0, 14, 0, 2, 8, 1, 4, 4, 5,
    4, 4, 1, 8, 2, 0, 14, 0, 1, 12, 0, 3, 8, 0, 7,
)
_COMB_ENDINGS = (
    (0, 12, 1, 4, 4, 1, 8, 0, 7),
    (0, 12, 1, 4, 4, 4, 4, 4, 1, 8, 0, 7),
    (0, 8, 3, 0, 12, 1, 4, 4, 5, 4, 4, 1, 8, 0, 7),
    (0, 12, 1, 4, 4, 1, 8, 2, 0, 14, 0, 1, 12, 0, 3, 8, 0, 7),
    (0, 12, 1, 4, 4, 4, 4, 4, 1, 8, 2, 0, 14, 0, 1, 12, 0, 3, 8, 0, 7),
    (0, 8, 3, 0, 12, 1, 4, 4, 5, 4, 4, 1, 8, 2, 0, 14, 0, 1, 12, 0, 3, 8, 0, 7),
    (0, 12, 1, 0, 14, 0, 2, 8, 1, 4, 4, 5, 4, 4, 1, 8, 2, 0, 14, 0, 1, 12, 0, 3, 8, 0, 7),
    (0, 12, 1, 4, 4, 1, 8, 2, 2, 2, 8, 1, 4, 4, 5, 4, 4, 1, 8, 2, 0, 14, 0, 1, 12, 0, 3, 8, 0, 7),
    (0, 8, 3, 0, 12, 1, 0, 14, 0, 2, 8, 1, 4, 4, 5, 4, 4, 1, 8, 2, 0, 14, 0, 1, 12, 0, 3, 8, 0, 7, 0, 0, 15),
    (0, 8, 3, 0, 12, 1, 4, 4, 5, 4, 4, 1, 8, 2, 2, 2, 8, 1, 4, 4, 5, 4, 4, 1, 8, 2, 0, 14, 0, 1, 12, 0, 3, 8, 0, 7),
)

# The three nonperiodic zipper witnesses of LowerZipper.lean, one mask per row.
_ZIPPER_BASES = {
    26: (
        67108861, 1, 33854025, 49320521, 33722953, 38310473, 38310473, 38441545,
        38310473, 38310473, 38310473, 38310473, 38310473, 38408777, 38294089,
        38343241, 38343241, 38359625, 38343241, 38343241, 38289993, 37898313,
        34752777, 43141409, 33554433, 41943037,
    ),
    29: (
        402653177, 268435457, 268435461, 402653169, 268435457, 268435469, 402653153,
        268435457, 268436637, 402649089, 268436449, 268584973, 402128897, 268566513,
        287571973, 335544321, 285212665, 301989889, 301989889, 318767101, 301989889,
        268435457, 301989885, 335544321, 268435457, 335544317, 268435457, 268435456,
        402653183,
    ),
    32: (
        3221225471, 2147483648, 2224179492, 2761050401, 2224179465, 2425505865,
        2450670153, 2453803593, 2454229577, 2454229577, 2454360649, 2454229577,
        2454229577, 2453836361, 2454753865, 2453967433, 2453967433, 2455016009,
        2453967433, 2453967433, 2454753865, 2453836361, 2454229577, 2454229577,
        2454360649, 2454229577, 2454229577, 2449642057, 2465239625, 2449773129,
        2147483649, 3221225469,
    ),
}


def square_score(n: int) -> int:
    """The exact square formula, including Lean's small-side cases."""
    if n < 1:
        raise ValueError("side length must be positive")
    k, remainder = divmod(n, 3)
    if remainder == 0:
        return 3 * k * k + 3 * k - 2
    if remainder == 1:
        return 1 if k == 0 else 3 * k * k + 5 * k + max(0, 3 * k - 13) // 10
    if k == 0:
        return 2
    if k < 5:
        return 3 * k * k + 7 * k + 1
    return 3 * k * k + 7 * k - (k - 5) // 7 - (n % 42 == 35)


def _comb(n: int) -> list[str]:
    loops, ending = divmod(n // 3 - 3, 10)
    word = (7,) + _COMB_LOOP * loops + _COMB_ENDINGS[ending]
    cap = ["".join("#" if col & (1 << row) else "." for col in word) for row in range(4)]
    rail = "#.." * (n // 3) + "#"
    return ["#" * n, "." * n] + [rail] * (n - 8) + cap + ["." * n, "#" * n]


def _zipper(n: int) -> list[str]:
    """Render the row layouts in LowerZipper.lean using sets of marked columns."""
    if n in _ZIPPER_BASES:
        return ["".join("#" if mask & (1 << j) else "." for j in range(n))
                for mask in _ZIPPER_BASES[n]]

    f, phase = (n - 2) // 6, n % 42

    def left(tip: int) -> set[int]:
        return set(range(0, tip + 1, 3))

    def right(start: int) -> set[int]:
        return set(range(start, n, 3))

    def regular(tip: int) -> set[int]:
        return left(tip) | right(tip + 4)

    def bands(start: int, tip: int, alternating: bool) -> None:
        for b, offset in enumerate(range(start, n - 5, 7)):
            rightward = alternating and b % 2 == 0
            width = min(7, n - 5 - offset)
            plain = regular(tip)
            for row in range(width):
                if row == 2:
                    marks.append(plain | {tip + 2})
                elif row >= 5 and width == 7:
                    drop = tip + 4 if rightward else tip
                    add = tip + 2 if row == 5 else (tip + 5 if rightward else tip - 1)
                    marks.append((plain - {drop}) | {add})
                else:
                    marks.append(plain.copy())
            if width == 7:
                tip += 3 if rightward else -3
        if alternating:
            outer = left(tip) | {n - 1}
            marks.extend([outer | {tip + 2}, outer | set(range(tip + 5, n - 2)),
                          outer | {tip + 3}, {0}, set(range(n)) - {1}])
        else:
            outer = left(tip - 6) | right(tip + 4)
            marks.extend([outer | {tip + 2}, outer | set(range(tip - 4, tip)),
                          outer | {tip + 1}, set(), set(range(n))])

    if phase == 14:
        marks = [{0} | set(range(3, n)), {0}]
        for i in range(f):
            l = 3 * i
            marks.append({0} | left(l - 1) | set(range(l + 2, n - 5 - l, 3)) | right(n - 1 - l))
        bands(f + 2, 3 * (f - 1), alternating=True)
    else:
        marks = [set(range(n - 3)) | {n - 1}, {n - 1}, right(2) | {n - 1}]
        for i in range(f):
            l, r = 3 * i, n - 1 - 3 * i
            marks.append(left(l) | set(range(l + 5, r - 4, 3)) | right(r))
        extra = {38: 1, 29: 1, 5: 2}.get(phase, 0)
        marks.extend(regular(3 * f) for _ in range(extra))
        bands(3 + f + extra, 3 * f, alternating=False)

        if n % 6 == 2 or phase in (5, 11, 29):
            if n % 6 == 2:
                end = 3 * f
            else:
                base, initial = {5: (47, 9), 11: (53, 9), 29: (71, 12)}[phase]
                end = initial + 6 * ((n - base) // 42)
            marks[0].remove(1)
            marks[1].add(0)
            for col in range(0, end + 1, 3):
                row = marks[2 + col // 3]
                row.add(col)
                if col < end:
                    row.remove(col + 2)

    return ["".join("#" if j in row else "." for j in range(n)) for row in marks]


def _mark_rows(n: int) -> list[str]:
    if n <= 3:
        return {1: ["#"], 2: ["##", ".."], 3: ["..#", "...", "###"]}[n]
    if n % 3 == 1 and n >= 16:
        return _comb(n)
    if n % 3 == 2 and n >= 23:
        return _zipper(n)
    pattern = (residue_zero_pattern, residue_one_pattern, residue_two_pattern)[n % 3]
    return [row.translate(str.maketrans(".U", "#.")) for row in pattern(n)]


def generate_square_tree(n: int) -> tuple[list[Edge], list[Vertex]]:
    """Return tree edges and the actual full-degree vertices, in grid coordinates."""
    score = square_score(n)
    rows = _mark_rows(n)
    if len(rows) != n or any(len(row) != n for row in rows):
        raise RuntimeError("construction returned a board of the wrong size")
    marked = "".join(rows)
    if marked.count("#") != score:
        raise RuntimeError(f"construction for side {n} did not mark {score} vertices")

    def grid_edges() -> Iterable[tuple[int, int]]:
        for u in range(n * n):
            if u % n < n - 1:
                yield u, u + 1
            if u + n < n * n:
                yield u, u + n

    parent = list(range(n * n))
    size = [1] * (n * n)
    degree = [0] * (n * n)
    edges = []

    def root(u: int) -> int:
        while parent[u] != u:
            parent[u] = parent[parent[u]]
            u = parent[u]
        return u

    # First keep all edges touching a marked vertex, then join the remaining
    # components with unforced grid edges. Never remove a forced edge.
    for forced in (True, False):
        for u, v in grid_edges():
            if ("#" in (marked[u], marked[v])) != forced:
                continue
            a, b = root(u), root(v)
            if a == b:
                if forced:
                    raise RuntimeError(f"forced edges form a cycle on side {n}")
                continue
            if size[a] < size[b]:
                a, b = b, a
            parent[b] = a
            size[a] += size[b]
            degree[u] += 1
            degree[v] += 1
            edges.append((divmod(u, n), divmod(v, n)))

    full = []
    for u, d in enumerate(degree):
        i, j = divmod(u, n)
        if d == (i > 0) + (i < n - 1) + (j > 0) + (j < n - 1):
            full.append((i, j))
    if len(edges) != n * n - 1 or len(full) != score:
        raise RuntimeError(f"completed tree on side {n} failed the edge or degree check")
    return edges, full


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("side", type=int, help="positive side length of the square grid")
    args = parser.parse_args()
    if args.side < 1:
        parser.error("side length must be positive")
    edges, full = generate_square_tree(args.side)
    json.dump({"side": args.side, "score": len(full), "full_degree_vertices": full, "edges": edges},
              sys.stdout, separators=(",", ":"))
    print()


if __name__ == "__main__":
    main()
