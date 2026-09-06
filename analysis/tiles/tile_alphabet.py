#!/usr/bin/env python3
"""Canonical 3x3 tile alphabet for diagonal U-patterns.

This module is the foundation for the tile-grammar synthesis program for
residues 0 and 2 of `n mod 3`. It defines:

* The named tile alphabet (slab S, cap C, bridge B, ...).
* Per-tile U-count and boundary U masks.
* Helpers to render tiles into U/. row-strings and to assemble tile matrices
  into an `n x n` U-pattern.

The boundary masks are subsets of `{0,1,2}` indicating which boundary cells
are U. A crossing U-U edge exists only when neighbouring tile masks overlap at
that position. These are inputs to, not complete descriptions of, the dual
routing interface needed by a future tile grammar.

Tiles are stored as 3x3 string tuples with `U` for non-full and `.` for full.
All tiles in this alphabet are aligned to the residue-1 phase: the canonical
slab tile is `... / UUU / UUU`, with rows ordered top to bottom and columns
left to right.
"""

from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class Tile:
    """A 3x3 U/. pattern with a canonical name and U-count."""

    name: str
    rows: tuple[str, str, str]

    @property
    def u_count(self) -> int:
        return sum(row.count("U") for row in self.rows)

    def cell(self, r: int, c: int) -> bool:
        return self.rows[r][c] == "U"

    # Boundary edges: for each side return the column / row indices where the
    # boundary cell is U (i.e. could form a U-U dual edge if its tile-neighbour
    # also carries U at the matching cell).
    @property
    def north_us(self) -> frozenset[int]:
        return frozenset(c for c in range(3) if self.cell(0, c))

    @property
    def south_us(self) -> frozenset[int]:
        return frozenset(c for c in range(3) if self.cell(2, c))

    @property
    def west_us(self) -> frozenset[int]:
        return frozenset(r for r in range(3) if self.cell(r, 0))

    @property
    def east_us(self) -> frozenset[int]:
        return frozenset(r for r in range(3) if self.cell(r, 2))

    def render(self) -> str:
        return "\n".join(self.rows)


# -----------------------------------------------------------------------------
# Named tile alphabet.
#
# These are the recurring tiles we observed across the cached witnesses for
# n = 12, 13, 14, 15. Names below are NOT the same as the auto-numbered
# C1, C2, ... in tile_class_matrix.py, which are local to each witness and
# permute with frequency. Names here are by ROLE, not by frequency.
# -----------------------------------------------------------------------------


# S = full slab. The default 6-U interior tile.
TILE_S = Tile(
    name="S",
    rows=(
        "...",
        "UUU",
        "UUU",
    ),
)

# C = 5-U cap, count-saving relative to S. Two dihedral copies appear in
# practice but for grammar purposes we use the canonical orientation.
# This is what every residue-1 strip uses on its left column.
TILE_C = Tile(
    name="C",
    rows=(
        "...",
        "UUU",
        ".UU",
    ),
)

# C' = mirror of C, used on the right side of a strip.
TILE_Cm = Tile(
    name="C'",
    rows=(
        "...",
        "UUU",
        "UU.",
    ),
)

# B = bridge tile, 6-U, used to splice two strips with different routing.
TILE_B = Tile(
    name="B",
    rows=(
        "..U",
        "UUU",
        "UU.",
    ),
)

# B' = mirror of B.
TILE_Bm = Tile(
    name="B'",
    rows=(
        "U..",
        "UUU",
        ".UU",
    ),
)

# K = 5-U corner cap variant used in residue-0 boundary patches.
# Appears as C4 in the n=15 witness.
TILE_K = Tile(
    name="K",
    rows=(
        "...",
        "UUU",
        "U.U",
    ),
)


ALPHABET: dict[str, Tile] = {
    t.name: t
    for t in (TILE_S, TILE_C, TILE_Cm, TILE_B, TILE_Bm, TILE_K)
}


def tile_grid_to_rows(grid: list[list[Tile]]) -> list[str]:
    """Assemble a tile matrix into U/. rows.

    `grid` is a list of `tile_rows` rows, each a list of `tile_cols` Tile
    objects. The output has `3 * tile_rows` rows of length `3 * tile_cols`.
    """
    out: list[str] = []
    for tile_row in grid:
        for r in range(3):
            line = "".join(tile.rows[r] for tile in tile_row)
            out.append(line)
    return out


def name(tile: Tile) -> str:
    return tile.name


__all__ = [
    "Tile",
    "ALPHABET",
    "TILE_S",
    "TILE_C",
    "TILE_Cm",
    "TILE_B",
    "TILE_Bm",
    "TILE_K",
    "tile_grid_to_rows",
    "name",
]
