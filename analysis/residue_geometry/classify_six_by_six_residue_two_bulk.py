#!/usr/bin/env python3
"""Classify density-one-third 6x6 periodic preserved-center bulks by rows."""

from __future__ import annotations

import argparse
import json
import math
from collections import Counter
from pathlib import Path
from analysis._paths import analysis_path


SIDE = 6
VERTICES = SIDE * SIDE
WEIGHT = VERTICES // 3
SCHEMA = "grid-graphs.six-by-six-residue-two-bulk.v1"
DEFAULT_OUTPUT = analysis_path("six_by_six_residue_two_bulk.json")
Vertex = tuple[int, int]
Voltage = tuple[int, int]


def adjacent_rows_valid(upper: int, lower: int) -> bool:
    """Check all six toroidal unit cells between two row masks."""
    for column in range(SIDE):
        following = (column + 1) % SIDE
        square = (
            (upper >> column) & 1,
            (upper >> following) & 1,
            (lower >> column) & 1,
            (lower >> following) & 1,
        )
        if sum(square) >= 3 or square[0] and square[3] or square[1] and square[2]:
            return False
    return True


def row_transition_table() -> tuple[tuple[int, ...], ...]:
    return tuple(
        tuple(lower for lower in range(1 << SIDE) if adjacent_rows_valid(upper, lower))
        for upper in range(1 << SIDE)
    )


def cyclic_row_walks(weight: int = WEIGHT) -> list[tuple[int, ...]]:
    """Enumerate closed six-step row walks, pruning by accumulated weight."""
    transitions = row_transition_table()
    walks: list[tuple[int, ...]] = []

    def extend(rows: tuple[int, ...], used: int) -> None:
        if len(rows) == SIDE:
            if used == weight and adjacent_rows_valid(rows[-1], rows[0]):
                walks.append(rows)
            return
        rows_left_after_choice = SIDE - len(rows) - 1
        for following in transitions[rows[-1]]:
            new_used = used + following.bit_count()
            if new_used <= weight <= new_used + SIDE * rows_left_after_choice:
                extend(rows + (following,), new_used)

    for first in range(1 << SIDE):
        extend((first,), first.bit_count())
    return walks


def cells(rows: tuple[int, ...]) -> set[Vertex]:
    return {
        (row, column)
        for row, mask in enumerate(rows)
        for column in range(SIDE)
        if mask & (1 << column)
    }


def render_rows(rows: tuple[int, ...]) -> list[str]:
    return [format(mask, "06b")[::-1] for mask in rows]


def quotient_edges(rows: tuple[int, ...]) -> list[tuple[int, int, Voltage]]:
    preserved = cells(rows)
    edges = []
    for row in range(SIDE):
        for column in range(SIDE):
            for d_row, d_column in ((0, 1), (1, 0)):
                other_row, other_column = row + d_row, column + d_column
                other = other_row % SIDE, other_column % SIDE
                if (row, column) in preserved or other in preserved:
                    edges.append((
                        SIDE * row + column,
                        SIDE * other[0] + other[1],
                        (other_row // SIDE, other_column // SIDE),
                    ))
    return edges


def quotient_cycle_data(rows: tuple[int, ...]) -> dict:
    """Apply the exact componentwise free-group/deck-voltage lift criterion."""
    edges = quotient_edges(rows)
    adjacency: list[list[tuple[int, Voltage, int]]] = [[] for _ in range(VERTICES)]
    for edge_index, (left, right, shift) in enumerate(edges):
        adjacency[left].append((right, shift, edge_index))
        adjacency[right].append((left, (-shift[0], -shift[1]), edge_index))

    potentials: list[Voltage | None] = [None] * VERTICES
    tree_edges: set[int] = set()
    components: list[list[int]] = []
    for root in range(VERTICES):
        if potentials[root] is not None:
            continue
        potentials[root] = (0, 0)
        component = []
        stack = [root]
        while stack:
            left = stack.pop()
            component.append(left)
            for right, shift, edge_index in adjacency[left]:
                if potentials[right] is None:
                    value = potentials[left]
                    assert value is not None
                    potentials[right] = value[0] + shift[0], value[1] + shift[1]
                    tree_edges.add(edge_index)
                    stack.append(right)
        components.append(component)

    component_of = {
        vertex: component_index
        for component_index, component in enumerate(components)
        for vertex in component
    }
    voltages: list[list[Voltage]] = [[] for _ in components]
    edge_counts = [0] * len(components)
    for edge_index, (left, right, shift) in enumerate(edges):
        component_index = component_of[left]
        edge_counts[component_index] += 1
        if edge_index not in tree_edges:
            left_value, right_value = potentials[left], potentials[right]
            assert left_value is not None and right_value is not None
            voltages[component_index].append((
                left_value[0] + shift[0] - right_value[0],
                left_value[1] + shift[1] - right_value[1],
            ))

    records = []
    lift_is_forest = True
    for component, edge_count, component_voltages in zip(components, edge_counts, voltages):
        rank = edge_count - len(component) + 1
        if rank >= 2:
            reason = "commutator_in_voltage_kernel"
        elif rank == 1 and component_voltages[0] == (0, 0):
            reason = "zero_voltage_generator"
        else:
            reason = "ok"
        lift_is_forest &= reason == "ok"
        records.append({
            "vertices": len(component),
            "edges": edge_count,
            "fundamental_rank": rank,
            "fundamental_cycle_voltages": [list(value) for value in component_voltages],
            "reason": reason,
        })
    return {
        "vertices": VERTICES,
        "edges": len(edges),
        "components": records,
        "lift_is_forest": lift_is_forest,
    }


def rows_from_cells(preserved: set[Vertex]) -> tuple[int, ...]:
    return tuple(
        sum(1 << column for column in range(SIDE) if (row, column) in preserved)
        for row in range(SIDE)
    )


def canonical_rows(rows: tuple[int, ...]) -> tuple[int, ...]:
    source = cells(rows)
    images = []
    for swap in (False, True):
        for sign_row in (-1, 1):
            for sign_column in (-1, 1):
                transformed = {
                    (
                        sign_row * (column if swap else row),
                        sign_column * (row if swap else column),
                    )
                    for row, column in source
                }
                for shift_row in range(SIDE):
                    for shift_column in range(SIDE):
                        images.append(rows_from_cells({
                            ((row + shift_row) % SIDE, (column + shift_column) % SIDE)
                            for row, column in transformed
                        }))
    return min(images)


def translation_periods(rows: tuple[int, ...]) -> list[list[int]]:
    source = cells(rows)
    return [
        [d_row, d_column]
        for d_row in range(SIDE)
        for d_column in range(SIDE)
        if {
            ((row + d_row) % SIDE, (column + d_column) % SIDE)
            for row, column in source
        } == source
    ]


def materialize(rows: tuple[int, ...], height: int, width: int) -> set[Vertex]:
    tile = cells(rows)
    return {
        (row, column)
        for row in range(height)
        for column in range(width)
        if (row % SIDE, column % SIDE) in tile
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


def gap_grammar_maximum(length: int) -> int:
    """Maximum singleton cap weight with two mandatory gaps after a site."""
    scores = {0: 0}
    for _ in range(length):
        following: dict[int, int] = {}
        for gap_counter, score in scores.items():
            empty_target = max(0, gap_counter - 1)
            following[empty_target] = max(following.get(empty_target, -1), score)
            if gap_counter == 0:
                following[2] = max(following.get(2, -1), score + 1)
        scores = following
    return max(scores.values())


def boundary_grammar(k: int, phase: int) -> dict:
    if k < 1 or phase not in (0, 1, 2):
        raise ValueError("require k >= 1 and phase in {0,1,2}")
    side_length = 3 * k + 2
    transverse_endpoints = 2 * k
    distances = (1 + phase, 3 - phase)
    cap_scores = []
    for distance in distances:
        if distance == 1:
            cap_scores.append(0)
        elif distance == 2:
            cap_scores.append(gap_grammar_maximum(side_length))
        else:
            cap_scores.append(side_length)
    return {
        "phase": phase,
        "parallel_cap_distances": list(distances),
        "transverse_endpoint_score": transverse_endpoints,
        "parallel_cap_scores": cap_scores,
        "maximum": transverse_endpoints + sum(cap_scores),
    }


def maximizing_family(k: int, phase: int) -> set[Vertex]:
    n = 3 * k + 2
    rail_rows = range(1 + phase, n - 1, 3)
    preserved = {(row, column) for row in rail_rows for column in range(n)}
    if phase == 0:
        preserved |= {(n - 1, column) for column in range(n)}
    elif phase == 2:
        preserved |= {(0, column) for column in range(n)}
    else:
        preserved |= {
            (row, column)
            for row in (0, n - 1)
            for column in range(1, n, 3)
        }
    return preserved


def build_report() -> dict:
    transitions = row_transition_table()
    walks = cyclic_row_walks()
    rejected = Counter()
    survivors = []
    for rows in walks:
        quotient = quotient_cycle_data(rows)
        if quotient["lift_is_forest"]:
            survivors.append((rows, quotient))
        else:
            bad_ranks = tuple(sorted(
                component["fundamental_rank"]
                for component in quotient["components"]
                if component["reason"] != "ok"
            ))
            rejected[bad_ranks] += 1

    survivor_records = [{
        "rows": render_rows(rows),
        "row_masks": list(rows),
        "canonical_row_masks": list(canonical_rows(rows)),
        "translation_stabilizer": translation_periods(rows),
        "quotient": quotient,
        "open_boxes_2_through_8": all(
            forced_forest(6 * repetitions, 6 * repetitions, materialize(rows, 6 * repetitions, 6 * repetitions))
            for repetitions in range(2, 9)
        ),
    } for rows, quotient in survivors]

    validation = []
    for k in (7, 8, 9):
        phases = []
        for phase in range(3):
            preserved = maximizing_family(k, phase)
            grammar = boundary_grammar(k, phase)
            phases.append({
                "phase": phase,
                "boundary_count": len(preserved) - 3 * k * k,
                "boundary_grammar_maximum": grammar["maximum"],
                "total": len(preserved),
                "forced_forest": forced_forest(3 * k + 2, 3 * k + 2, preserved),
            })
        validation.append({
            "k": k,
            "n": 3 * k + 2,
            "target": 3 * k * k + 7 * k,
            "phases": phases,
        })

    checks_ok = (
        len(survivors) == 6
        and len({canonical_rows(rows) for rows, _ in survivors}) == 1
        and all(
            phase["boundary_count"] == phase["boundary_grammar_maximum"]
            and phase["forced_forest"]
            for record in validation
            for phase in record["phases"]
        )
    )
    return {
        "schema": SCHEMA,
        "status": "complete_six_by_six_obstruction" if checks_ok else "check_failure",
        "scope": {
            "period": "6x6 torus",
            "density": "12/36=1/3",
            "all_weight_twelve_masks": math.comb(VERTICES, WEIGHT),
            "enumeration_method": "closed length-six walks in the 64-state row automaton, pruned to total weight 12",
            "not_enumerated": "the 2^36 masks and the C(36,12) fixed-weight masks",
            "boundary_family": "width-one cap with straight intervals, singleton star intersections, and forest incidence",
        },
        "row_automaton": {
            "states": 1 << SIDE,
            "directed_transitions": sum(len(targets) for targets in transitions),
            "closed_weight_twelve_walks": len(walks),
            "unit_cell_rule": "reject three or four centers, and reject either diagonal pair, in every cyclic 2x2 cell",
        },
        "bulk_classification": {
            "local_weight_twelve_survivors": len(walks),
            "symbolic_forced_forest_survivors": len(survivors),
            "quotient_rejections_by_bad_component_ranks": {
                ",".join(map(str, ranks)): count for ranks, count in sorted(rejected.items())
            },
            "torus_dihedral_orbits": len({canonical_rows(rows) for rows, _ in survivors}),
            "representative_row_masks": list(min(canonical_rows(rows) for rows, _ in survivors)),
            "survivors": survivor_records,
            "derived_topology": {
                "primitive_periods": "3x1 horizontal rails or 1x3 vertical rails",
                "phases": "three transverse translations in each of two orientations",
                "incidence": "two quotient components; each is a rank-one rail with one nonzero longitudinal voltage",
                "bulk_count_in_3k_by_3k_core": "3k^2",
            },
        },
        "symbolic_criterion": {
            "statement": "each quotient component must have free rank zero, or free rank one with nonzero Z^2 deck voltage",
            "nonabelian_obstruction": "rank at least two has a nontrivial free-group commutator in the kernel of every abelian voltage map",
            "zero_voltage_obstruction": "a rank-one zero-voltage generator lifts to a finite cycle",
        },
        "boundary_grammar": {
            "state": "row phase; cap distance 1,2,3; singleton gap counter 0,1,2; endpoint and corner ownership",
            "singleton_transitions": "occupied 0->2 with weight 1; empty s->max(0,s-1)",
            "phase_formulas": {
                "0": "2k + 0 + (3k+2) = 5k+2",
                "1": "2k + (k+1) + (k+1) = 4k+2",
                "2": "2k + (3k+2) + 0 = 5k+2",
            },
            "maximum_boundary_linear_term": "5k+2",
            "maximum_total": "3k^2+5k+2",
        },
        "target_decision": {
            "target": "3k^2+7k",
            "attainable_for_all_k_at_least_7": False,
            "deficit": "2k-2",
            "validated_deficits": {str(k): 2 * k - 2 for k in (7, 8, 9)},
            "periodic_scope_exhausted": "yes for density-one-third 6x6 bulks (and their lower primitive periods), not for arbitrary larger periods",
            "construction_decision": "no target candidate survives; every survivor is the already-obstructed parallel-rail construction",
        },
        "validation": validation,
        "checks": {
            "row_walk_accounting": len(survivors) + sum(rejected.values()) == len(walks),
            "six_survivors": len(survivors) == 6,
            "one_torus_dihedral_orbit": len({canonical_rows(rows) for rows, _ in survivors}) == 1,
            "all_survivors_have_primitive_rail_topology": all(
                len(quotient["components"]) == 2
                and all(component["fundamental_rank"] == 1 for component in quotient["components"])
                for _, quotient in survivors
            ),
            "k_7_8_9_formulas_and_forests": checks_ok,
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
        print(f"6x6 classification matches {args.output}")
    else:
        args.output.write_text(rendered)
        print(f"wrote {args.output}")


if __name__ == "__main__":
    main()
