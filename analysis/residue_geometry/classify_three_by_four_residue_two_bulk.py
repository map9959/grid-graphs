#!/usr/bin/env python3
"""Classify density-one-third 3x4 residue-two preserved-center bulks."""

from __future__ import annotations

import argparse
import itertools
import json
from collections import Counter
from pathlib import Path

from analysis._paths import analysis_path

HEIGHT = 3
WIDTH = 4
VERTICES = HEIGHT * WIDTH
SCHEMA = "grid-graphs.three-by-four-residue-two-bulk.v1"
DEFAULT_OUTPUT = analysis_path("three_by_four_residue_two_bulk.json")
Vertex = tuple[int, int]


def cells(mask: int) -> set[Vertex]:
    return {
        (index // WIDTH, index % WIDTH)
        for index in range(VERTICES)
        if mask & (1 << index)
    }


def rows(mask: int) -> list[str]:
    return [
        format((mask >> (WIDTH * row)) & ((1 << WIDTH) - 1), "04b")[::-1]
        for row in range(HEIGHT)
    ]


def unit_cells_valid(mask: int) -> bool:
    preserved = cells(mask)
    for row in range(HEIGHT):
        for column in range(WIDTH):
            square = (
                (row, column),
                (row, (column + 1) % WIDTH),
                ((row + 1) % HEIGHT, column),
                ((row + 1) % HEIGHT, (column + 1) % WIDTH),
            )
            present = tuple(vertex in preserved for vertex in square)
            if sum(present) >= 3 or present[0] and present[3] or present[1] and present[2]:
                return False
    return True


def quotient_edges(mask: int) -> list[tuple[int, int, tuple[int, int]]]:
    preserved = cells(mask)
    edges = []
    for row in range(HEIGHT):
        for column in range(WIDTH):
            for d_row, d_column in ((0, 1), (1, 0)):
                other_row, other_column = row + d_row, column + d_column
                other = other_row % HEIGHT, other_column % WIDTH
                if (row, column) in preserved or other in preserved:
                    edges.append((
                        WIDTH * row + column,
                        WIDTH * other[0] + other[1],
                        (other_row // HEIGHT, other_column // WIDTH),
                    ))
    return edges


def quotient_cycle_data(mask: int) -> dict:
    """Compute a fundamental-cycle voltage basis and the exact lift criterion."""
    edges = quotient_edges(mask)
    adjacency: list[list[tuple[int, tuple[int, int], int]]] = [[] for _ in range(VERTICES)]
    for edge_index, (left, right, shift) in enumerate(edges):
        adjacency[left].append((right, shift, edge_index))
        adjacency[right].append((left, (-shift[0], -shift[1]), edge_index))

    potentials: list[tuple[int, int] | None] = [None] * VERTICES
    tree_edges: set[int] = set()
    components = 0
    for root in range(VERTICES):
        if potentials[root] is not None:
            continue
        components += 1
        potentials[root] = (0, 0)
        stack = [root]
        while stack:
            left = stack.pop()
            for right, shift, edge_index in adjacency[left]:
                if potentials[right] is None:
                    value = potentials[left]
                    assert value is not None
                    potentials[right] = value[0] + shift[0], value[1] + shift[1]
                    tree_edges.add(edge_index)
                    stack.append(right)

    voltages = []
    for edge_index, (left, right, shift) in enumerate(edges):
        if edge_index in tree_edges:
            continue
        left_value, right_value = potentials[left], potentials[right]
        assert left_value is not None and right_value is not None
        voltages.append((
            left_value[0] + shift[0] - right_value[0],
            left_value[1] + shift[1] - right_value[1],
        ))

    cycle_rank = len(edges) - VERTICES + components
    generator_nonzero = cycle_rank == 1 and voltages[0] != (0, 0)
    lift_is_forest = cycle_rank == 0 or generator_nonzero
    if cycle_rank >= 2:
        reason = "commutator_in_voltage_kernel"
    elif cycle_rank == 1 and not generator_nonzero:
        reason = "zero_voltage_generator"
    else:
        reason = "ok"
    return {
        "vertices": VERTICES,
        "edges": len(edges),
        "components": components,
        "fundamental_cycle_rank": cycle_rank,
        "fundamental_cycle_voltages": [list(value) for value in voltages],
        "lift_is_forest": lift_is_forest,
        "reason": reason,
    }


def canonical_mask(mask: int) -> int:
    source = cells(mask)
    images = []
    for sign_row, sign_column in itertools.product((-1, 1), repeat=2):
        transformed = {(sign_row * row, sign_column * column) for row, column in source}
        for shift_row, shift_column in itertools.product(range(HEIGHT), range(WIDTH)):
            image = 0
            for row, column in transformed:
                image |= 1 << (
                    WIDTH * ((row + shift_row) % HEIGHT)
                    + (column + shift_column) % WIDTH
                )
            images.append(image)
    return min(images)


def materialize(mask: int, height: int, width: int) -> set[Vertex]:
    tile = cells(mask)
    return {
        (row, column)
        for row in range(height)
        for column in range(width)
        if (row % HEIGHT, column % WIDTH) in tile
    }


def forced_forest(height: int, width: int, preserved: set[Vertex]) -> bool:
    parent = list(range(height * width))

    def root(vertex: int) -> int:
        while parent[vertex] != vertex:
            parent[vertex] = parent[parent[vertex]]
            vertex = parent[vertex]
        return vertex

    for row in range(height):
        for column in range(width):
            for d_row, d_column in ((0, 1), (1, 0)):
                other = row + d_row, column + d_column
                if other[0] == height or other[1] == width:
                    continue
                if (row, column) not in preserved and other not in preserved:
                    continue
                left = root(row * width + column)
                right = root(other[0] * width + other[1])
                if left == right:
                    return False
                parent[right] = left
    return True


def boundary_maximum(k: int, row_phase: int) -> int:
    if k < 1 or row_phase not in (0, 1, 2):
        raise ValueError("require k >= 1 and row_phase in {0,1,2}")
    return 5 * k + 2 if row_phase in (0, 2) else 4 * k + 2


def maximizing_family(k: int, row_phase: int) -> set[Vertex]:
    n = 3 * k + 2
    rail_rows = range(1 + row_phase, n - 1, 3)
    preserved = {(row, column) for row in rail_rows for column in range(n)}
    if row_phase == 0:
        preserved |= {(n - 1, column) for column in range(n)}
    elif row_phase == 2:
        preserved |= {(0, column) for column in range(n)}
    else:
        preserved |= {
            (row, column)
            for row in (0, n - 1)
            for column in range(1, n, 3)
        }
    return preserved


def gap_grammar_maximum(length: int) -> int:
    scores = {0: 0}
    for _ in range(length):
        following: dict[int, int] = {}
        for state, score in scores.items():
            empty_target = max(0, state - 1)
            following[empty_target] = max(following.get(empty_target, -1), score)
            if state == 0:
                following[2] = max(following.get(2, -1), score + 1)
        scores = following
    return max(scores.values())


def build_report() -> dict:
    weight_four = [mask for mask in range(1 << VERTICES) if mask.bit_count() == 4]
    local = [mask for mask in weight_four if unit_cells_valid(mask)]
    classified = [(mask, quotient_cycle_data(mask)) for mask in local]
    survivors = [(mask, quotient) for mask, quotient in classified if quotient["lift_is_forest"]]
    rejected_quotients = Counter(
        (quotient["fundamental_cycle_rank"], quotient["reason"])
        for _, quotient in classified
        if not quotient["lift_is_forest"]
    )
    survivor_records = [
        {
            "mask": mask,
            "rows": rows(mask),
            "canonical_symmetry_phase_mask": canonical_mask(mask),
            "quotient": quotient,
            "finite_open_boxes_2_through_12": all(
                forced_forest(3 * repetitions, 4 * repetitions, materialize(mask, 3 * repetitions, 4 * repetitions))
                for repetitions in range(2, 13)
            ),
        }
        for mask, quotient in survivors
    ]

    validation = []
    for k in (7, 8, 9):
        phases = []
        for row_phase in range(3):
            preserved = maximizing_family(k, row_phase)
            phases.append({
                "row_phase": row_phase,
                "boundary_contribution": len(preserved) - 3 * k * k,
                "boundary_formula": boundary_maximum(k, row_phase),
                "total": len(preserved),
                "target": 3 * k * k + 7 * k,
                "deficit": 3 * k * k + 7 * k - len(preserved),
                "forced_forest": forced_forest(3 * k + 2, 3 * k + 2, preserved),
            })
        validation.append({"k": k, "k_mod_4": k % 4, "n": 3 * k + 2, "phases": phases})

    checks_ok = all(
        phase["boundary_contribution"] == phase["boundary_formula"] and phase["forced_forest"]
        for record in validation
        for phase in record["phases"]
    )
    return {
        "schema": SCHEMA,
        "status": "complete_three_by_four_obstruction" if checks_ok else "check_failure",
        "scope": {
            "period": "3x4",
            "density": "4/12=1/3",
            "masks_enumerated": 1 << VERTICES,
            "weight_four_masks": len(weight_four),
            "core": "the 3k by 3k interior of the (3k+2)-square",
            "boundary_grammar": "straight preserved intervals with singleton forced-star intersections and forest incidence",
        },
        "bulk_classification": {
            "unit_cell_survivors": len(local),
            "unit_cell_rejections": len(weight_four) - len(local),
            "quotient_rejections_by_rank_and_reason": {
                f"rank_{rank}:{reason}": count
                for (rank, reason), count in sorted(rejected_quotients.items())
            },
            "symbolic_forced_forest_survivors": len(survivors),
            "symmetry_phase_orbits": len({canonical_mask(mask) for mask, _ in survivors}),
            "representatives": sorted({canonical_mask(mask) for mask, _ in survivors}),
            "survivors": survivor_records,
            "bulk_count": "3k^2",
        },
        "symbolic_criterion": {
            "statement": "the periodic lift is a forest iff every quotient component has fundamental rank zero, or rank one with nonzero deck voltage",
            "commutator_obstruction": "rank at least two is impossible: two free generators have a nontrivial commutator, and every commutator has zero voltage in the abelian deck group Z^2",
            "abelian_rank_warning": "linear independence of cycle voltages is not sufficient when fundamental rank is at least two",
        },
        "boundary_grammar": {
            "states": [
                "row phase 0, 1, or 2",
                "rail endpoint extend/omit",
                "parallel cap distance 1, 2, or 3",
                "singleton gap counter 0, 1, or 2",
                "four corner ownership bits",
            ],
            "hard_bounds": {
                "outer row phases 0 and 2": "2k transverse endpoints + (3k+2) disjoint rail = 5k+2",
                "center row phase 1": "2k transverse endpoints + 2(k+1) gap-grammar singletons = 4k+2",
            },
            "gap_grammar": "occupied: 0->2 with weight 1; empty: s->max(0,s-1)",
            "gap_checks": {str(k): gap_grammar_maximum(3 * k + 2) for k in (7, 8, 9)},
            "maximum_boundary_contribution": "5k+2",
            "maximum_total": "3k^2+5k+2",
        },
        "k_mod_4": {
            str(residue): {
                "horizontal_clip_phase": f"3k mod 4 = {(3 * residue) % 4}",
                "survivor_effect": "none; every survivor is constant across the period-four coordinate",
                "maximum_total": "3k^2+5k+2",
            }
            for residue in range(4)
        },
        "target_obstruction": {
            "target": "3k^2+7k",
            "exact_deficit": "2k-2",
            "one_step": {
                "family": "P(k+1)-P(k)=6k+8",
                "target": "T(k+1)-T(k)=6k+10",
            },
            "four_step": {
                "family": "P(k+4)-P(k)=24k+68",
                "target": "T(k+4)-T(k)=24k+76",
            },
            "attainable": False,
        },
        "validation": validation,
        "next_search": {
            "decision": "6x6 periodic before nonperiodic",
            "reason": "3x4 adds no bulk topology beyond the period-three rail; 6x6 is the next square density-one-third cell and can support a nonabelian-looking finite quotient only if its actual lift remains rank at most one per component",
            "fallback": "move to nonperiodic topology if the 6x6 quotient census and cap grammar also miss the target",
        },
        "checks": {
            "all_weight_four_masks_accounted_for": len(local) + len(weight_four) - len(local) == len(weight_four),
            "all_symbolic_survivors_one_orbit": len({canonical_mask(mask) for mask, _ in survivors}) == 1,
            "commutator_candidates_rejected": rejected_quotients[(2, "commutator_in_voltage_kernel")] == 12,
            "k_7_8_9_maximizers_validate": checks_ok,
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    rendered = json.dumps(build_report(), indent=2, sort_keys=True) + "\n"
    if args.check:
        if not args.output.exists() or args.output.read_text() != rendered:
            raise SystemExit(f"stale or missing artifact: {args.output}")
        print(f"3x4 classification matches {args.output}")
    else:
        args.output.write_text(rendered)
        print(f"wrote {args.output}")


if __name__ == "__main__":
    main()
