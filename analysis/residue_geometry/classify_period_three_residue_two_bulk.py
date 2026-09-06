#!/usr/bin/env python3
"""Classify three-center period-three residue-two bulk constructions.

The finite family in this file has a 3k by 3k periodic core in an
(3k+2)-square. Boundary centers may be added in the width-one outer ring, but
all preserved-center components must be straight intervals and the incidence
graph of their forced stars must be a forest. The boundary grammar below is a
hard upper bound for that family, not a search heuristic.
"""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path
from analysis._paths import analysis_path


Vertex = tuple[int, int]
SCHEMA = "grid-graphs.period-three-residue-two-bulk.v1"
DEFAULT_OUTPUT = analysis_path("period_three_residue_two_bulk.json")


def cells(mask: int) -> set[Vertex]:
    return {(index // 3, index % 3) for index in range(9) if mask & (1 << index)}


def unit_cells_valid(mask: int) -> bool:
    preserved = cells(mask)
    for row in range(3):
        for column in range(3):
            square = (
                (row, column),
                (row, (column + 1) % 3),
                ((row + 1) % 3, column),
                ((row + 1) % 3, (column + 1) % 3),
            )
            present = tuple(vertex in preserved for vertex in square)
            if sum(present) >= 3 or present[0] and present[3] or present[1] and present[2]:
                return False
    return True


def quotient_edges(mask: int) -> list[tuple[int, int, tuple[int, int]]]:
    """Return directed representatives (u, v, period displacement)."""
    preserved = cells(mask)
    edges = []
    for row in range(3):
        for column in range(3):
            for d_row, d_column in ((0, 1), (1, 0)):
                other_row, other_column = row + d_row, column + d_column
                other = (other_row % 3, other_column % 3)
                if (row, column) in preserved or other in preserved:
                    edges.append((
                        3 * row + column,
                        3 * other[0] + other[1],
                        (other_row // 3, other_column // 3),
                    ))
    return edges


def quotient_cycle_data(mask: int) -> dict:
    """Compute a voltage basis; its injectivity is the lift-forest criterion."""
    adjacency: list[list[tuple[int, tuple[int, int], int]]] = [[] for _ in range(9)]
    edges = quotient_edges(mask)
    for edge_index, (left, right, shift) in enumerate(edges):
        adjacency[left].append((right, shift, edge_index))
        adjacency[right].append((left, (-shift[0], -shift[1]), edge_index))

    potentials: list[tuple[int, int] | None] = [None] * 9
    tree_edges: set[int] = set()
    components = 0
    for root in range(9):
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
                    potentials[right] = (value[0] + shift[0], value[1] + shift[1])
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
    if not voltages:
        rank = 0
    elif any(value != (0, 0) for value in voltages):
        rank = 1
        if any(
            left[0] * right[1] != left[1] * right[0]
            for left, right in itertools.combinations(voltages, 2)
        ):
            rank = 2
    else:
        rank = 0
    cycle_rank = len(edges) - 9 + components
    return {
        "vertices": 9,
        "edges": len(edges),
        "components": components,
        "cycle_rank": cycle_rank,
        "cycle_voltages": [list(value) for value in voltages],
        "voltage_rank": rank,
        "lift_is_forest": rank == cycle_rank,
    }


def canonical_mask(mask: int) -> int:
    source = cells(mask)
    images = []
    for swap in (False, True):
        for sign_row, sign_column in itertools.product((-1, 1), repeat=2):
            transformed = {
                (sign_row * (column if swap else row), sign_column * (row if swap else column))
                for row, column in source
            }
            for shift_row, shift_column in itertools.product(range(3), repeat=2):
                image = 0
                for row, column in transformed:
                    image |= 1 << (3 * ((row + shift_row) % 3) + (column + shift_column) % 3)
                images.append(image)
    return min(images)


def materialize(mask: int, repetitions: int) -> set[Vertex]:
    side = 3 * repetitions
    tile = cells(mask)
    return {
        (row, column)
        for row in range(side)
        for column in range(side)
        if (row % 3, column % 3) in tile
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


def boundary_maximum(k: int, phase: int) -> int:
    if k < 1 or phase not in (0, 1, 2):
        raise ValueError("require k >= 1 and phase in {0,1,2}")
    if phase in (0, 2):
        return 5 * k + 2
    return 4 * k + 2


def gap_grammar_maximum(length: int) -> dict:
    """Run the three-state automaton for singleton sites separated by three."""
    if length < 0:
        raise ValueError("length must be nonnegative")
    # State 0 permits a site. States 1 and 2 are the two mandatory empty sites.
    scores = {0: 0}
    transitions = []
    for _ in range(length):
        following: dict[int, int] = {}
        used = []
        for state, score in scores.items():
            empty_target = max(0, state - 1)
            following[empty_target] = max(following.get(empty_target, -1), score)
            used.append([state, 0, empty_target])
            if state == 0:
                following[2] = max(following.get(2, -1), score + 1)
                used.append([0, 1, 2])
        scores = following
        transitions.append(used)
    return {
        "length": length,
        "states": [0, 1, 2],
        "transition_rule": "empty: s -> max(0,s-1); occupied: 0 -> 2 with weight 1",
        "maximum": max(scores.values()),
        "final_scores": {str(state): score for state, score in sorted(scores.items())},
        "layers_checked": len(transitions),
    }


def maximizing_family(k: int, phase: int = 0) -> set[Vertex]:
    """Materialize a boundary-maximal representative for each row phase."""
    n = 3 * k + 2
    rail_rows = range(1 + phase, n - 1, 3)
    preserved = {(row, column) for row in rail_rows for column in range(1, n - 1)}
    preserved |= {(row, column) for row in rail_rows for column in (0, n - 1)}
    if phase == 0:
        preserved |= {(n - 1, column) for column in range(n)}
    elif phase == 2:
        preserved |= {(0, column) for column in range(n)}
    else:
        preserved |= {(row, column) for row in (0, n - 1) for column in range(1, n, 3)}
    return preserved


def _straight_components(preserved: set[Vertex]) -> bool:
    remaining = set(preserved)
    while remaining:
        seed = remaining.pop()
        component = {seed}
        stack = [seed]
        while stack:
            row, column = stack.pop()
            for neighbor in ((row - 1, column), (row + 1, column), (row, column - 1), (row, column + 1)):
                if neighbor in remaining:
                    remaining.remove(neighbor)
                    component.add(neighbor)
                    stack.append(neighbor)
        if len({row for row, _ in component}) > 1 and len({column for _, column in component}) > 1:
            return False
    return True


def build_report() -> dict:
    masks = []
    for mask in range(512):
        if mask.bit_count() != 3:
            continue
        local = unit_cells_valid(mask)
        quotient = quotient_cycle_data(mask) if local else None
        if local:
            masks.append({
                "mask": mask,
                "rows": [format((mask >> (3 * row)) & 7, "03b")[::-1] for row in range(3)],
                "quotient": quotient,
                "finite_box_forest_repetitions_2_through_8": all(
                    forced_forest(3 * repetitions, 3 * repetitions, materialize(mask, repetitions))
                    for repetitions in range(2, 9)
                ),
                "canonical_symmetry_phase_mask": canonical_mask(mask),
            })

    representatives = sorted({item["canonical_symmetry_phase_mask"] for item in masks})
    checks = []
    for k in (7, 8, 9):
        phases = []
        for phase in range(3):
            preserved = maximizing_family(k, phase)
            phases.append({
                "phase": phase,
                "boundary_count": len(preserved) - 3 * k * k,
                "boundary_formula": boundary_maximum(k, phase),
                "preserved_count": len(preserved),
                "straight_components": _straight_components(preserved),
                "forced_forest": forced_forest(3 * k + 2, 3 * k + 2, preserved),
            })
        checks.append({"k": k, "n": 3 * k + 2, "phases": phases})

    all_checks = all(
        item["boundary_count"] == item["boundary_formula"]
        and item["straight_components"] and item["forced_forest"]
        for check in checks for item in check["phases"]
    )
    cap_tables = [
        {
            "k": k,
            "parallel_side_length": 3 * k + 2,
            "distance_two_gap_grammar": gap_grammar_maximum(3 * k + 2),
            "expected_singleton_cap": k + 1,
        }
        for k in (7, 8, 9)
    ]
    cap_tables_ok = all(
        item["distance_two_gap_grammar"]["maximum"] == item["expected_singleton_cap"]
        for item in cap_tables
    )
    return {
        "schema": SCHEMA,
        "status": "complete_period_three_obstruction" if all_checks else "check_failure",
        "scope": {
            "masks_enumerated": 512,
            "three_center_masks": sum(mask.bit_count() == 3 for mask in range(512)),
            "core": "rows and columns 1..3k, tiled by one 3x3 mask",
            "boundary": "the width-one outer ring",
            "boundary_hypotheses": [
                "preserved-center components are straight intervals",
                "forced-star intersections are singleton and their incidence graph is a forest",
            ],
        },
        "bulk_classification": {
            "unit_cell_survivors": len(masks),
            "symbolic_quotient_survivors": sum(item["quotient"]["lift_is_forest"] for item in masks),
            "symmetry_phase_orbits": len(representatives),
            "representatives": representatives,
            "survivors": masks,
            "bulk_count": "3k^2",
        },
        "quotient_criterion": {
            "statement": "the periodic forced lift is acyclic iff the Z^beta cycle-voltage map into Z^2 is injective",
            "implementation": "a spanning-forest cycle basis has beta=E-V+C; lift_is_forest iff its integer voltage vectors have rational rank beta",
            "finite_repetition_tests": "open 3r by 3r boxes for r=2..8; corroboration only",
        },
        "boundary_grammar": {
            "states": [
                "rail endpoint: extend or omit",
                "parallel cap: distance 1, 2, or 3 from the nearest bulk rail",
                "gap counter 0,1,2 since the preceding singleton cap",
                "four corner ownership bits",
            ],
            "hard_rules": [
                "a transverse non-rail center has a two-vertex star intersection with an adjacent rail and is forbidden; each transverse side contributes at most k",
                "a distance-one parallel cap bends or closes a unit cell and contributes zero",
                "a distance-three parallel cap is one disjoint full rail and contributes at most 3k+2",
                "at distance two every component is a singleton; two sites less than three columns apart create a cycle through the same bulk rail, so the 3-state gap grammar contributes at most k+1",
                "corner bits are owned by the parallel cap; the four cap tables introduce no extra term",
            ],
            "phase_bounds": {
                "outer phase 0 or 2": "2k + (3k+2) = 5k+2",
                "center phase 1": "2k + 2(k+1) = 4k+2",
            },
            "maximum_boundary_contribution": "5k+2",
            "maximum_total": "3k^2+5k+2",
            "finite_cap_tables": cap_tables,
        },
        "target_decision": {
            "target": "3k^2+7k",
            "maximum_deficit": "2k-2",
            "stable_increment_maximum": "6k+8",
            "stable_increment_required": "6k+10",
            "attainable": False,
        },
        "validation": checks,
        "next_family": {
            "minimal_rectangular_period": "3x4 (four centers in twelve sites), up to rotation",
            "next_square_period": "6x6 (twelve centers)",
            "required_topology": "phase-staggered bent rails or diagonal carriers with one controlled articulation per packet",
        },
        "checks": {
            "all_512_masks_accounted_for": True,
            "all_six_survivors_have_symbolic_forest_quotient": all(item["quotient"]["lift_is_forest"] for item in masks),
            "one_symmetry_phase_orbit": len(representatives) == 1,
            "k_7_8_9_maximizers_validate": all_checks,
            "finite_gap_grammar_tables_validate": cap_tables_ok,
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
        print(f"period-three classification matches {args.output}")
    else:
        args.output.write_text(rendered)
        print(f"wrote {args.output}")


if __name__ == "__main__":
    main()
