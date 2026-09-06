#!/usr/bin/env python3
"""Search an n→n+3 tile production with a free inserted row and column."""

from __future__ import annotations

import argparse
from functools import cache
from itertools import product
from pathlib import Path

from analysis.patterns.construction_lab import q_formula, run_check
from analysis.patterns.diagonal_patterns import residue_zero_explicit_pattern
from analysis.tiles.tile_alphabet import Tile
from analysis.tiles.tile_grammar import (
    production_tiles,
    suffix_u_costs,
    synthesize_domains_bidirectional,
)
from analysis.tiles.tile_symmetry import orbit


@cache
def all_tiles_with_cost(cost: int):
    """All 3x3 U-patterns with one fixed U count."""
    tiles = []
    for cells in product(".U", repeat=9):
        if cells.count("U") != cost:
            continue
        rows = tuple("".join(cells[3 * row : 3 * row + 3]) for row in range(3))
        tiles.append(Tile(f"P{cost}_{len(tiles):03}", rows))
    return tuple(tiles)


def read_pattern(path: Path) -> list[str]:
    rows = [line.strip() for line in path.read_text().splitlines() if line.strip()]
    if not rows or any(len(row) != len(rows) for row in rows):
        raise ValueError("source pattern must be a nonempty square")
    if len(rows) % 3:
        raise ValueError("source width must be divisible by three")
    return rows


def source_tiles(rows: list[str]):
    by_rows = {tile.rows: tile for tile in production_tiles(oriented=True)}
    k = len(rows) // 3
    matrix = []
    for tile_r in range(k):
        matrix_row = []
        for tile_c in range(k):
            block = tuple(
                rows[3 * tile_r + local_r][3 * tile_c : 3 * tile_c + 3]
                for local_r in range(3)
            )
            matrix_row.append(
                by_rows.get(block, Tile(f"S{tile_r}_{tile_c}", block))
            )
        matrix.append(matrix_row)
    return matrix


def inserted_cross_domains(
    rows: list[str],
    row_insert: int,
    col_insert: int,
    old_classes: bool = False,
    copy_row: int | None = None,
    copy_col: int | None = None,
    rewrite_radius: int = 0,
    free_old: frozenset[tuple[int, int]] = frozenset(),
    free_old_patterns: bool = False,
    free_old_bands: frozenset[int] = frozenset(),
):
    """Keep old tiles exact and make the inserted tile row and column free."""
    old = source_tiles(rows)
    k = len(old)
    if not 0 <= row_insert <= k or not 0 <= col_insert <= k:
        raise ValueError("tile insertion indices must lie between old tile bands")
    tiles = production_tiles(oriented=True)
    if copy_row is not None and not 0 <= copy_row < k:
        raise ValueError("copied tile row is out of range")
    if copy_col is not None and not 0 <= copy_col < k:
        raise ValueError("copied tile column is out of range")
    if rewrite_radius < 0:
        raise ValueError("rewrite radius must be nonnegative")
    if any(old_r < 0 or old_r >= k for old_r in free_old_bands):
        raise ValueError("free preserved band is out of range")

    def class_domain(source):
        variants = orbit(source.rows)
        return tuple(tile for tile in tiles if tile.rows in variants)

    domains = []
    for tile_r in range(k + 1):
        domain_row = []
        for tile_c in range(k + 1):
            if tile_r == row_insert and tile_c == col_insert:
                if copy_row is None or copy_col is None:
                    domain_row.append(tiles)
                else:
                    domain_row.append(class_domain(old[copy_row][copy_col]))
                continue
            if tile_r == row_insert:
                if copy_row is None:
                    domain_row.append(tiles)
                else:
                    old_c = tile_c if tile_c < col_insert else tile_c - 1
                    domain_row.append(class_domain(old[copy_row][old_c]))
                continue
            if tile_c == col_insert:
                if copy_col is None:
                    domain_row.append(tiles)
                else:
                    old_r = tile_r if tile_r < row_insert else tile_r - 1
                    domain_row.append(class_domain(old[old_r][copy_col]))
                continue
            old_r = tile_r if tile_r < row_insert else tile_r - 1
            old_c = tile_c if tile_c < col_insert else tile_c - 1
            source = old[old_r][old_c]
            if old_r in free_old_bands:
                domain_row.append(
                    tuple(tile for tile in tiles if tile.u_count == source.u_count)
                )
            elif (old_r, old_c) in free_old:
                domain_row.append(
                    all_tiles_with_cost(source.u_count) if free_old_patterns else tiles
                )
            elif (
                rewrite_radius
                and abs(tile_r - row_insert) <= rewrite_radius
                and abs(tile_c - col_insert) <= rewrite_radius
            ):
                domain_row.append(
                    tuple(tile for tile in tiles if tile.u_count == source.u_count)
                )
            elif old_classes:
                domain_row.append(class_domain(source))
            else:
                domain_row.append((source,))
        domains.append(domain_row)
    return domains


def observed_transfer_domains(rows: list[str]):
    """Transfer the best n=12→15 class-level insertion footprint one step."""
    old = source_tiles(rows)
    k = len(old)
    if k < 4:
        raise ValueError("observed transfer requires at least four tile bands")
    row_insert = 2
    col_insert = 0
    domains = inserted_cross_domains(rows, row_insert, col_insert)
    tiles = production_tiles(oriented=True)

    def cost_domain(source):
        return tuple(tile for tile in tiles if tile.u_count == source.u_count)

    # The inserted n=15 row is one corner class followed by bridge classes.
    for tile_c in range(k + 1):
        source_c = min(tile_c, k - 1)
        domains[row_insert][tile_c] = cost_domain(old[2][source_c])

    # Extend the observed left-column profile by repeating its penultimate
    # interior role before the final boundary role.
    for tile_r in range(k + 1):
        if tile_r < k - 1:
            source_r = tile_r
        elif tile_r == k - 1:
            source_r = k - 2
        else:
            source_r = k - 1
        domains[tile_r][col_insert] = cost_domain(old[source_r][0])

    footprint = {(1, 1), (1, 2), (2, 0), (2, 1), (2, 3), (3, 2)}
    changed_old = footprint | {
        (old_r + 1, old_c)
        for old_r, old_c in footprint
        if old_r + 1 < k
    }
    for old_r, old_c in changed_old:
        tile_r = old_r + (old_r >= row_insert)
        tile_c = old_c + (old_c >= col_insert)
        cost = old[old_r][old_c].u_count
        domains[tile_r][tile_c] = tuple(
            tile for tile in tiles if tile.u_count == cost
        )
    return domains


def require_cut_bridge(
    domains: list[list[tuple[Tile, ...]]], bridge_column: int, require_u: bool = True
) -> None:
    """Expand the two cut tiles, optionally forcing one crossing U-U edge."""
    require_cut_bridges(domains, (bridge_column,), require_u=require_u)


def require_cut_bridges(
    domains: list[list[tuple[Tile, ...]]],
    bridge_columns: tuple[int, ...],
    require_u: bool = True,
) -> None:
    """Expand cut tiles while retaining every requested crossing constraint."""
    tile_rows = len(domains)
    if tile_rows < 2 or any(len(row) != tile_rows for row in domains):
        raise ValueError("bridge domains must form a square tile matrix")
    n = 3 * tile_rows
    if not bridge_columns:
        return
    if any(not 0 <= bridge_column < n for bridge_column in bridge_columns):
        raise ValueError("bridge column is outside the synthesized grid")
    split = (tile_rows + 1) // 2

    def expanded(
        domain: tuple[Tile, ...], local_r: int, local_columns: set[int]
    ) -> tuple[Tile, ...]:
        costs = {tile.u_count for tile in domain}
        return tuple(
            tile
            for cost in sorted(costs)
            for tile in all_tiles_with_cost(cost)
            if not require_u
            or all(tile.rows[local_r][local_c] == "U" for local_c in local_columns)
        )

    by_tile: dict[int, set[int]] = {}
    for bridge_column in bridge_columns:
        tile_c, local_c = divmod(bridge_column, 3)
        by_tile.setdefault(tile_c, set()).add(local_c)
    for tile_c, local_columns in by_tile.items():
        domains[split - 1][tile_c] = expanded(
            domains[split - 1][tile_c], 2, local_columns
        )
        domains[split][tile_c] = expanded(
            domains[split][tile_c], 0, local_columns
        )


def expand_pattern_domains(
    domains: list[list[tuple[Tile, ...]]], positions: frozenset[tuple[int, int]]
) -> None:
    """Replace selected synthesized tile domains by all patterns of their costs."""
    tile_rows = len(domains)
    for tile_r, tile_c in positions:
        if not 0 <= tile_r < tile_rows or not 0 <= tile_c < tile_rows:
            raise ValueError("free pattern tile position is out of range")
        costs = {tile.u_count for tile in domains[tile_r][tile_c]}
        domains[tile_r][tile_c] = tuple(
            tile for cost in sorted(costs) for tile in all_tiles_with_cost(cost)
        )


def apply_cost_profile(
    domains: list[list[tuple[Tile, ...]]],
    profile: dict[tuple[int, int], int],
    use_all_patterns: bool = False,
) -> int:
    """Apply fixed tile costs and return their net change from the domains."""
    tile_rows = len(domains)
    oriented = production_tiles(oriented=True)
    delta = 0
    for (tile_r, tile_c), target_cost in profile.items():
        if not 0 <= tile_r < tile_rows or not 0 <= tile_c < tile_rows:
            raise ValueError("cost profile tile position is out of range")
        old_costs = {tile.u_count for tile in domains[tile_r][tile_c]}
        if len(old_costs) == 1:
            old_cost = next(iter(old_costs))
            delta += target_cost - old_cost
        elif target_cost not in old_costs:
            raise ValueError("cost profile is outside a mixed baseline domain")
        replacement = (
            all_tiles_with_cost(target_cost)
            if use_all_patterns
            else tuple(tile for tile in oriented if tile.u_count == target_cost)
        )
        if not replacement:
            raise ValueError(f"no production tiles have U cost {target_cost}")
        domains[tile_r][tile_c] = replacement
    return delta


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "source",
        help="source pattern path, or a cached explicit residue-0 grid size",
    )
    parser.add_argument("row_insert", type=int, nargs="?")
    parser.add_argument("col_insert", type=int, nargs="?")
    parser.add_argument("--all-insertions", action="store_true")
    parser.add_argument("--observed-transfer", action="store_true")
    parser.add_argument("--beam", type=int, default=100)
    parser.add_argument("--max-cycle-excess", type=int, default=1)
    parser.add_argument(
        "--prefix-beam",
        type=int,
        default=1000,
        help="maximum partial states retained after each tile in a free band",
    )
    parser.add_argument("--copy-row", type=int)
    parser.add_argument("--copy-col", type=int)
    parser.add_argument("--rewrite-radius", type=int, default=0)
    parser.add_argument(
        "--free-old",
        action="append",
        default=[],
        metavar="ROW,COL",
        help="free a preserved source-tile position; may be repeated",
    )
    parser.add_argument(
        "--free-old-patterns",
        action="store_true",
        help="use every same-cost 3x3 pattern at --free-old positions",
    )
    parser.add_argument(
        "--free-old-band",
        action="append",
        default=[],
        type=int,
        metavar="ROW",
        help="free a complete preserved source tile band within per-tile U costs",
    )
    parser.add_argument(
        "--bridge-column",
        action="append",
        default=[],
        type=int,
        help="require a U-U cut crossing; may be repeated",
    )
    parser.add_argument(
        "--expand-cut-column",
        type=int,
        help="expand the two cut tiles at this column without forcing a crossing",
    )
    parser.add_argument(
        "--free-pattern",
        action="append",
        default=[],
        metavar="TILE_ROW,TILE_COL",
        help="use every same-cost pattern at a synthesized tile position",
    )
    parser.add_argument(
        "--tile-cost",
        action="append",
        default=[],
        metavar="TILE_ROW,TILE_COL=COST",
        help="override a fixed synthesized tile cost; may be repeated",
    )
    parser.add_argument(
        "--cost-patterns",
        action="store_true",
        help="use every 3x3 pattern, rather than oriented tiles, at cost overrides",
    )
    parser.add_argument(
        "--target-side",
        choices=("forward", "backward"),
        default="backward",
        help="half whose final beam is ranked against the opposite frontier",
    )
    parser.add_argument("--split", type=int, help="tile-band index of the meet cut")
    parser.add_argument(
        "--old-classes",
        action="store_true",
        help="allow old tiles to rotate or reflect within their dihedral class",
    )
    args = parser.parse_args()
    if args.bridge_column and args.expand_cut_column is not None:
        parser.error("choose at most one of --bridge-column and --expand-cut-column")
    if args.split is not None and (args.bridge_column or args.expand_cut_column is not None):
        parser.error("custom --split is not supported with cut-bridge constraints")

    source = (
        residue_zero_explicit_pattern(int(args.source))
        if args.source.isdecimal()
        else read_pattern(Path(args.source))
    )
    try:
        free_old = frozenset(
            tuple(int(value) for value in position.split(","))
            for position in args.free_old
        )
    except ValueError as error:
        parser.error(f"invalid --free-old position: {error}")
    if any(len(position) != 2 for position in free_old):
        parser.error("--free-old positions must have the form ROW,COL")
    try:
        free_patterns = frozenset(
            tuple(int(value) for value in position.split(","))
            for position in args.free_pattern
        )
    except ValueError as error:
        parser.error(f"invalid --free-pattern position: {error}")
    if any(len(position) != 2 for position in free_patterns):
        parser.error("--free-pattern positions must have the form ROW,COL")
    cost_profile = {}
    try:
        for specification in args.tile_cost:
            position_text, cost_text = specification.split("=", 1)
            position = tuple(int(value) for value in position_text.split(","))
            if len(position) != 2:
                raise ValueError("position must have the form ROW,COL")
            cost_profile[position] = int(cost_text)
    except ValueError as error:
        parser.error(f"invalid --tile-cost specification: {error}")
    n = len(source) + 3
    target = q_formula(n)
    k = len(source) // 3
    if args.observed_transfer:
        if args.row_insert is not None or args.col_insert is not None:
            parser.error("do not give insertion indices with --observed-transfer")
        insertions = [(2, 0)]
    elif args.all_insertions:
        if args.row_insert is not None or args.col_insert is not None:
            parser.error("do not give insertion indices with --all-insertions")
        insertions = [(row, col) for row in range(k + 1) for col in range(k + 1)]
    else:
        if args.row_insert is None or args.col_insert is None:
            parser.error("give row_insert and col_insert, or use --all-insertions")
        insertions = [(args.row_insert, args.col_insert)]

    total_transitions = 0
    for row_insert, col_insert in insertions:
        if args.observed_transfer:
            domains = observed_transfer_domains(source)
        else:
            domains = inserted_cross_domains(
                source,
                row_insert,
                col_insert,
                args.old_classes,
                args.copy_row,
                args.copy_col,
                args.rewrite_radius,
                free_old,
                args.free_old_patterns,
                frozenset(args.free_old_band),
            )
        try:
            profile_delta = apply_cost_profile(
                domains, cost_profile, use_all_patterns=args.cost_patterns
            )
        except ValueError as error:
            parser.error(str(error))
        expand_pattern_domains(domains, free_patterns)
        if args.bridge_column:
            require_cut_bridges(domains, tuple(args.bridge_column))
        if args.expand_cut_column is not None:
            require_cut_bridge(domains, args.expand_cut_column, require_u=False)
        costs = suffix_u_costs(domains)[0]
        inserted_tiles = 2 * k + 1
        inserted_cost = target - q_formula(len(source)) - profile_delta
        inserted_six = inserted_cost - 5 * inserted_tiles
        print(
            f"row_insert={row_insert} col_insert={col_insert} "
            f"profile_delta={profile_delta} inserted_cost={inserted_cost} "
            f"inserted_six={inserted_six}"
        )
        if target not in costs:
            print(f"row_insert={row_insert} col_insert={col_insert} cost-infeasible")
            continue
        diagnostics = {}
        rows, names, transitions, side_counts = synthesize_domains_bidirectional(
            domains,
            target,
            None if args.beam <= 0 else args.beam,
            max_cycle_excess=args.max_cycle_excess,
            partial_beam_width=None if args.prefix_beam <= 0 else args.prefix_beam,
            diagnostics=diagnostics,
            target_rank_side=args.target_side,
            split=args.split,
        )
        total_transitions += transitions
        print(
            f"row_insert={row_insert} col_insert={col_insert} "
            f"transitions={transitions} sides={side_counts} "
            f"merge={diagnostics} found={rows is not None}"
        )
        if rows is None:
            continue
        info = run_check(n, rows, verbose=True)
        print(f"tile bands={names}")
        for row in rows:
            print(row)
        if not info["all_ok"]:
            raise SystemExit("grammar produced an invalid candidate")
        return

    qualifier = "exhaustive" if args.beam <= 0 else "beam-limited"
    print(
        f"no {qualifier} production found across {len(insertions)} alignments; "
        f"transitions={total_transitions}"
    )
    raise SystemExit(1)


if __name__ == "__main__":
    main()
