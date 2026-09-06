#!/usr/bin/env python3
"""Search an unaligned three-row/column insertion into a cached witness."""

from __future__ import annotations

import argparse
from functools import cache
from itertools import product

from analysis.patterns.construction_lab import q_formula, run_check
from analysis.patterns.diagonal_patterns import residue_zero_explicit_pattern
from analysis.tiles.tile_alphabet import Tile
from analysis.tiles.tile_grammar import synthesize_domains_bidirectional


@cache
def constrained_tiles(
    template: tuple[str | None, ...], allowed_costs: tuple[int, ...]
) -> tuple[Tile, ...]:
    """Enumerate 3x3 patterns matching fixed cells in one aligned target tile."""
    free = [index for index, value in enumerate(template) if value is None]
    tiles = []
    for values in product(".U", repeat=len(free)):
        cells = list(template)
        for index, value in zip(free, values):
            cells[index] = value
        rows = tuple(
            "".join(cells[3 * local_r : 3 * local_r + 3])
            for local_r in range(3)
        )
        if sum(row.count("U") for row in rows) not in allowed_costs:
            continue
        tiles.append(Tile(f"X{len(tiles):03}", rows))
    return tuple(tiles)


def phase_shifted_domains(
    source: list[str],
    row_start: int,
    col_start: int,
    allowed_costs: tuple[int, ...] = (5, 6),
) -> list[list[tuple[Tile, ...]]]:
    """Fix the embedded source outside an unaligned width-three cross."""
    old_n = len(source)
    if old_n % 3 or any(len(row) != old_n for row in source):
        raise ValueError("source must be square with width divisible by three")
    if not 0 <= row_start <= old_n or not 0 <= col_start <= old_n:
        raise ValueError("insertion starts must lie between source rows and columns")
    n = old_n + 3
    tile_rows = n // 3
    domains = []
    for tile_r in range(tile_rows):
        domain_row = []
        for tile_c in range(tile_rows):
            template: list[str | None] = []
            for local_r in range(3):
                r = 3 * tile_r + local_r
                for local_c in range(3):
                    c = 3 * tile_c + local_c
                    if (
                        row_start <= r < row_start + 3
                        or col_start <= c < col_start + 3
                    ):
                        template.append(None)
                        continue
                    old_r = r if r < row_start else r - 3
                    old_c = c if c < col_start else c - 3
                    template.append(source[old_r][old_c])
            domain = constrained_tiles(tuple(template), allowed_costs)
            if not domain:
                raise ValueError(
                    f"tile ({tile_r},{tile_c}) has no pattern at costs {allowed_costs}"
                )
            domain_row.append(domain)
        domains.append(domain_row)
    return domains


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("source", type=int, nargs="?", default=18)
    parser.add_argument("row_start", type=int, nargs="?")
    parser.add_argument("col_start", type=int, nargs="?")
    parser.add_argument("--all-phase", action="store_true")
    parser.add_argument("--row-range", default="8:14", metavar="START:STOP")
    parser.add_argument("--col-range", default="3:9", metavar="START:STOP")
    parser.add_argument("--costs", default="5,6")
    parser.add_argument("--beam", type=int, default=50)
    parser.add_argument("--prefix-beam", type=int, default=100)
    parser.add_argument(
        "--target-side", choices=("forward", "backward"), default="backward"
    )
    parser.add_argument("--split", type=int, help="tile-band index of the meet cut")
    args = parser.parse_args()

    try:
        allowed_costs = tuple(sorted({int(value) for value in args.costs.split(",")}))
        row_lo, row_hi = (int(value) for value in args.row_range.split(":"))
        col_lo, col_hi = (int(value) for value in args.col_range.split(":"))
    except ValueError as error:
        parser.error(f"invalid range or cost list: {error}")
    if not allowed_costs:
        parser.error("--costs must not be empty")
    if args.all_phase:
        if args.row_start is not None or args.col_start is not None:
            parser.error("do not give insertion starts with --all-phase")
        starts = list(product(range(row_lo, row_hi), range(col_lo, col_hi)))
    else:
        if args.row_start is None or args.col_start is None:
            parser.error("give row_start and col_start, or use --all-phase")
        starts = [(args.row_start, args.col_start)]

    source = residue_zero_explicit_pattern(args.source)
    n = len(source) + 3
    target = q_formula(n)
    total_transitions = 0
    for row_start, col_start in starts:
        try:
            domains = phase_shifted_domains(
                source, row_start, col_start, allowed_costs
            )
        except ValueError as error:
            print(f"rows={row_start} cols={col_start} infeasible: {error}")
            continue
        diagnostics: dict[str, object] = {}
        rows, names, transitions, sides = synthesize_domains_bidirectional(
            domains,
            target,
            beam_width=None if args.beam <= 0 else args.beam,
            partial_beam_width=(
                None if args.prefix_beam <= 0 else args.prefix_beam
            ),
            diagnostics=diagnostics,
            target_rank_side=args.target_side,
            split=args.split,
        )
        total_transitions += transitions
        print(
            f"rows={row_start} cols={col_start} transitions={transitions} "
            f"sides={sides} merge={diagnostics} found={rows is not None}"
        )
        if rows is None:
            continue
        info = run_check(n, rows, verbose=True)
        print(f"tile bands={names}")
        print("\n".join(rows))
        if not info["all_ok"]:
            raise SystemExit("phase-shifted grammar produced an invalid candidate")
        return
    print(
        f"no beam-limited phase-shifted production across {len(starts)} geometries; "
        f"transitions={total_transitions}"
    )
    raise SystemExit(1)


if __name__ == "__main__":
    main()
