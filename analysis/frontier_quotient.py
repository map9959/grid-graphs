#!/usr/bin/env python3
"""Verify exact cross-width frontier anchors for a residue-zero quotient."""

from __future__ import annotations

from collections import defaultdict

from diagonal_patterns import residue_zero_explicit_pattern
from tile_alphabet import Tile
from tile_grammar import (
    advance_band,
    band_trace,
    frontier_key,
    initial_state,
    production_tiles,
    projected_frontier_key,
    row_mask,
)


def removed_cross_cost(
    rows: list[str], processed_rows: int, row_start: int, col_start: int
) -> int:
    return sum(
        rows[r][c] == "U"
        for r in range(processed_rows)
        for c in range(len(rows))
        if row_start <= r < row_start + 3 or col_start <= c < col_start + 3
    )


def normalize_projected_row(key: tuple, row_shift: int) -> tuple:
    row_index, mask, partition, cost, cycles = key
    return row_index - row_shift, mask, partition, cost, cycles


def verify_residue_zero_anchors() -> None:
    """Pin the exact n=15/n=18 prefix and shifted-tail frontier equalities."""
    old_rows = residue_zero_explicit_pattern(15)
    new_rows = residue_zero_explicit_pattern(18)
    row_start = 9
    col_start = 4

    for r in range(18):
        for c in range(18):
            if row_start <= r < row_start + 3 or col_start <= c < col_start + 3:
                continue
            old_r = r if r < row_start else r - 3
            old_c = c if c < col_start else c - 3
            if new_rows[r][c] != old_rows[old_r][old_c]:
                raise AssertionError(f"outside-cross mismatch at ({r},{c})")

    old = {
        state.row_index: state
        for state in band_trace(old_rows)
        if state is not None
    }
    new = {
        state.row_index: state
        for state in band_trace(new_rows)
        if state is not None
    }
    anchors = (
        (3, 3, 0),
        (6, 6, 0),
        (12, 15, 3),
        (15, 18, 3),
    )
    costs = tuple(
        removed_cross_cost(new_rows, new_row, row_start, col_start)
        for _, new_row, _ in anchors
    )
    if costs != (5, 12, 58, 63):
        raise AssertionError(f"anchor removal costs changed: {costs}")

    for (old_row, new_row, row_shift), removed in zip(anchors, costs):
        projected = projected_frontier_key(
            new[new_row], col_start, 3, removed
        )
        if normalize_projected_row(projected, row_shift) != frontier_key(old[old_row]):
            raise AssertionError(
                f"frontier anchor mismatch: old row {old_row}, new row {new_row}"
            )

    if old[12].finished or new[15].finished:
        raise AssertionError("tail-entry anchors must remain unfinished")
    if not old[15].finished or not new[18].finished:
        raise AssertionError("final anchors must be finished")


def replace_slab_tile(
    rows: list[str], band_index: int, slab_start: int, tile: Tile
) -> tuple[int, int, int]:
    """Replace one 3x3 slab block while retaining the fixed n=18 exterior."""
    row_start = 3 * band_index
    return tuple(
        row_mask(
            rows[row_start + local_row][:slab_start]
            + tile.rows[local_row]
            + rows[row_start + local_row][slab_start + 3 :]
        )
        for local_row in range(3)
    )  # type: ignore[return-value]


def verify_one_band_collision_audit() -> None:
    """Show that naive slab projection is not a one-band right congruence."""
    rows = residue_zero_explicit_pattern(18)
    slab_start = 4
    tiles = production_tiles(oriented=True)
    by_name = {tile.name: tile for tile in tiles}
    first = {}
    quotient_classes: dict[tuple, list[str]] = defaultdict(list)

    for tile in tiles:
        state = advance_band(
            initial_state(18), replace_slab_tile(rows, 0, slab_start, tile)
        )
        if state is None:
            continue
        first[tile.name] = (state, tile.u_count)
        quotient_classes[
            projected_frontier_key(state, slab_start, 3, tile.u_count)
        ].append(tile.name)

    if len(first) != 8 or sorted(map(len, quotient_classes.values())) != [1, 2, 5]:
        raise AssertionError("first-band quotient collision artifact changed")
    expected_classes = {
        frozenset(("O02", "O03", "O04", "O14", "O21")),
        frozenset(("O13", "O22")),
        frozenset(("O23",)),
    }
    if {frozenset(names) for names in quotient_classes.values()} != expected_classes:
        raise AssertionError("first-band quotient classes changed")

    pairs = {}
    sealed = 0
    for first_tile in tiles:
        first_record = first.get(first_tile.name)
        for second_tile in tiles:
            if first_record is None:
                sealed += 1
                continue
            first_state, first_removed = first_record
            state = advance_band(
                first_state,
                replace_slab_tile(rows, 1, slab_start, second_tile),
            )
            if state is None:
                sealed += 1
                continue
            pairs[(first_tile.name, second_tile.name)] = (
                state,
                first_removed + second_tile.u_count,
            )
    if len(pairs) != 3 or sealed != 573:
        raise AssertionError(
            f"one-band audit counts changed: live={len(pairs)}, sealed={sealed}"
        )

    state_02, removed_02 = first["O02"]
    state_03, removed_03 = first["O03"]
    if projected_frontier_key(
        state_02, slab_start, 3, removed_02
    ) != projected_frontier_key(state_03, slab_start, 3, removed_03):
        raise AssertionError("expected O02/O03 quotient collision disappeared")

    child_02, removed_child_02 = pairs[("O02", "O20")]
    child_03, removed_child_03 = pairs[("O03", "O20")]
    quotient_02 = projected_frontier_key(
        child_02, slab_start, 3, removed_child_02
    )
    quotient_03 = projected_frontier_key(
        child_03, slab_start, 3, removed_child_03
    )
    if quotient_02[:-1] != quotient_03[:-1] or quotient_02[-1] != 1 or quotient_03[-1] != 3:
        raise AssertionError("expected hidden-cycle quotient counterexample changed")


def main() -> None:
    verify_residue_zero_anchors()
    verify_one_band_collision_audit()
    print("verified n=15/n=18 quotient anchors at prefix and shifted tail")
    print("verified 24x24 one-band quotient collision audit")
    print("counterexample: O02 ~ O03, but O02/O20 and O03/O20 have cycles 1 and 3")
    print("cost decomposition: 12 + (4n - 14) + 5 = 4n + 3")
    print("n=21 state target: cost 240 before an exact cost-35 cap")


if __name__ == "__main__":
    main()
