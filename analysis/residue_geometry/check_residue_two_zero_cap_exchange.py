#!/usr/bin/env python3
"""Check the fixed-hub outer-arm residue-zero cap-exchange grammar.

The source is the proved residue-zero phase family on the 3k square.  It is
embedded in the top-left corner of the (3k+2) square.  The old bottom cap is
first deleted.  The declared grammar may reinsert that cap unchanged and may
put forced vertices on the outermost row and column.  Every maximal outer run
must have at most one attachment to the old rooted interval tree.

All eight masks in every three-position packet are admitted.  A two-state
dynamic program therefore exhausts the grammar without enumerating arbitrary
subsets of the two-cell frame.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Iterable

from analysis.patterns.diagonal_patterns import residue_zero_phase_pattern
from analysis._paths import analysis_path


Vertex = tuple[int, int]
Edge = tuple[Vertex, Vertex]
SCHEMA = "grid-graphs.residue-two-zero-cap-exchange.v1"
DEFAULT_OUTPUT = analysis_path("residue_two_zero_cap_exchange.json")


def _neighbors(vertex: Vertex, n: int) -> Iterable[Vertex]:
    row, column = vertex
    if row:
        yield row - 1, column
    if row + 1 < n:
        yield row + 1, column
    if column:
        yield row, column - 1
    if column + 1 < n:
        yield row, column + 1


def _components(vertices: set[Vertex], n: int) -> list[frozenset[Vertex]]:
    remaining = set(vertices)
    result = []
    while remaining:
        seed = min(remaining)
        remaining.remove(seed)
        component = {seed}
        pending = [seed]
        while pending:
            vertex = pending.pop()
            for neighbor in _neighbors(vertex, n):
                if neighbor in remaining:
                    remaining.remove(neighbor)
                    component.add(neighbor)
                    pending.append(neighbor)
        result.append(frozenset(component))
    return result


def _straight(component: frozenset[Vertex]) -> bool:
    rows = {row for row, _ in component}
    columns = {column for _, column in component}
    if len(rows) == 1:
        coordinates = sorted(column for _, column in component)
    elif len(columns) == 1:
        coordinates = sorted(row for row, _ in component)
    else:
        return False
    return coordinates == list(range(coordinates[0], coordinates[-1] + 1))


def _star(component: frozenset[Vertex], n: int) -> tuple[frozenset[Edge], frozenset[Vertex]]:
    edges = {
        tuple(sorted((vertex, neighbor)))
        for vertex in component
        for neighbor in _neighbors(vertex, n)
    }
    return frozenset(edges), frozenset(vertex for edge in edges for vertex in edge)


def _is_acyclic(edges: frozenset[Edge]) -> bool:
    parent: dict[Vertex, Vertex] = {}

    def find(vertex: Vertex) -> Vertex:
        parent.setdefault(vertex, vertex)
        while parent[vertex] != vertex:
            parent[vertex] = parent[parent[vertex]]
            vertex = parent[vertex]
        return vertex

    for left, right in sorted(edges):
        left_root, right_root = find(left), find(right)
        if left_root == right_root:
            return False
        parent[right_root] = left_root
    return True


def _interval_incidence(
    components: list[frozenset[Vertex]], n: int
) -> tuple[int, int, bool]:
    supports = [_star(component, n)[1] for component in components]
    links = 0
    maximum_intersection = 0
    adjacency = [set() for _ in components]
    for left in range(len(components)):
        for right in range(left + 1, len(components)):
            intersection = supports[left] & supports[right]
            maximum_intersection = max(maximum_intersection, len(intersection))
            if intersection:
                links += len(intersection)
                adjacency[left].add(right)
                adjacency[right].add(left)
    reached = set()
    if components:
        reached.add(0)
        pending = [0]
        while pending:
            for neighbor in adjacency[pending.pop()] - reached:
                reached.add(neighbor)
                pending.append(neighbor)
    return links, maximum_intersection, len(reached) == len(components)


def _unit_cell_violations(forced: set[Vertex], n: int) -> list[Vertex]:
    return [
        (row, column)
        for row in range(n - 1)
        for column in range(n - 1)
        if sum(
            vertex in forced
            for vertex in (
                (row, column),
                (row + 1, column),
                (row, column + 1),
                (row + 1, column + 1),
            )
        ) >= 3
    ]


def _maximum_single_attachment_word(touches: list[bool]) -> tuple[int, str]:
    """Maximize selected sites with at most one touch in each selected run."""
    # State is (previous site selected, touches in current run).
    states: dict[tuple[bool, int], tuple[int, str]] = {(False, 0): (0, "")}
    for touches_core in touches:
        successors: dict[tuple[bool, int], tuple[int, str]] = {}
        for (selected, run_touches), (count, word) in states.items():
            skipped = successors.get((False, 0))
            if skipped is None or count > skipped[0]:
                successors[(False, 0)] = count, word + "0"
            next_touches = (run_touches if selected else 0) + int(touches_core)
            if next_touches <= 1:
                taken = successors.get((True, next_touches))
                if taken is None or count + 1 > taken[0]:
                    successors[(True, next_touches)] = count + 1, word + "1"
        states = successors
    return max(states.values())


def analyze_k(k: int) -> dict:
    if k < 7:
        raise ValueError("the residue-zero phase source requires k >= 7")
    old_n, n = 3 * k, 3 * k + 2
    rows = residue_zero_phase_pattern(old_n)
    source = {
        (row, column)
        for row, values in enumerate(rows)
        for column, value in enumerate(values)
        if value == "."
    }
    deleted_cap = {(old_n - 1, column) for column in range(old_n) if column != 1}
    retained = source - deleted_cap

    source_components = _components(source, n)
    retained_components = _components(retained, n)
    source_stars = [_star(component, n) for component in source_components]
    source_edges = frozenset().union(*(edges for edges, _ in source_stars))
    source_support = frozenset().union(*(support for _, support in source_stars))
    source_links, source_max_intersection, source_connected = _interval_incidence(
        source_components, n
    )
    retained_links, retained_max_intersection, _ = _interval_incidence(
        retained_components, n
    )

    # Traverse the outer L as one path, with the corner occurring once.
    outer_path = [
        *((row, n - 1) for row in range(n)),
        *((n - 1, column) for column in range(n - 2, -1, -1)),
    ]
    touches = []
    for vertex in outer_path:
        singleton_edges, _ = _star(frozenset({vertex}), n)
        new_edges = singleton_edges - source_edges
        new_support = {endpoint for edge in new_edges for endpoint in edge}
        touches.append(bool(new_support & source_support))
    outer_capacity, maximizing_word = _maximum_single_attachment_word(touches)

    target_forced = 3 * k * k + 7 * k
    retained_count = len(retained)
    replacement_required = target_forced - retained_count
    grammar_capacity = len(deleted_cap) + outer_capacity
    checks = {
        "source_count": len(source) == 3 * k * k + 3 * k - 2,
        "deleted_cap_count": len(deleted_cap) == 3 * k - 1,
        "retained_count": retained_count == 3 * k * k - 1,
        "replacement_required": replacement_required == 7 * k + 1,
        "source_components_straight": all(map(_straight, source_components)),
        "retained_components_straight": all(map(_straight, retained_components)),
        "source_unit_cells_valid": not _unit_cell_violations(source, n),
        "source_star_intersections_singleton": source_max_intersection <= 1,
        "source_incidence_tree": source_connected
        and source_links == len(source_components) - 1,
        "source_forced_forest": _is_acyclic(source_edges),
        "retained_star_intersections_singleton": retained_max_intersection <= 1,
        "source_component_formula": len(source_components) == 3 * k - 1,
        "retained_component_formula": len(retained_components) == 3 * k - 2,
        "retained_link_formula": retained_links == 2 * k - 2,
        "outer_path_formula": len(outer_path) == 6 * k + 3,
        "outer_touch_formula": sum(touches) == 6 * k - 4,
        "outer_capacity_formula": outer_capacity == 3 * k + 5,
        "grammar_capacity_formula": grammar_capacity == 6 * k + 4,
        "grammar_is_below_target": grammar_capacity < replacement_required,
    }
    return {
        "k": k,
        "n": n,
        "status": "obstructed" if all(checks.values()) else "claim_mismatch",
        "counts": {
            "source_forced": len(source),
            "deleted_bottom_cap": len(deleted_cap),
            "retained_forced": retained_count,
            "target_forced": target_forced,
            "required_replacement": replacement_required,
            "outer_arm_capacity": outer_capacity,
            "fixed_hub_grammar_capacity": grammar_capacity,
            "deficit": replacement_required - grammar_capacity,
        },
        "source_interval_skeleton": {
            "nodes": len(source_components),
            "links": source_links,
            "maximum_star_intersection": source_max_intersection,
            "tree": source_connected and source_links == len(source_components) - 1,
        },
        "retained_interval_forest": {
            "nodes": len(retained_components),
            "links": retained_links,
            "components": len(retained_components) - retained_links,
            "maximum_star_intersection": retained_max_intersection,
        },
        "outer_arm_grammar": {
            "path_length": len(outer_path),
            "root_touch_count": sum(touches),
            "root_free_count": len(touches) - sum(touches),
            "root_touch_word": "".join("1" if value else "0" for value in touches),
            "canonical_maximizing_word": maximizing_word,
            "rule": "every maximal selected run contains at most one root-touch site",
            "packet_alphabet": "all eight binary masks on each consecutive three-site packet",
            "enumeration": "exact two-state dynamic program over the outer L path",
        },
        "stable_interface": {
            "required_replacement_step": 7,
            "grammar_capacity_step": 6,
            "step_deficit": 1,
            "minimum_inner_layer_credit": k - 3,
        },
        "checks": checks,
    }


def build_report(ks: tuple[int, ...] = (7, 8, 9)) -> dict:
    records = [analyze_k(k) for k in ks]
    return {
        "schema": SCHEMA,
        "checker": "residue_two_zero_cap_exchange",
        "status": "complete_grammar_obstruction"
        if all(record["status"] == "obstructed" for record in records)
        else "claim_mismatch",
        "k_values": list(ks),
        "declared_grammar": {
            "retained_core": "top-left residue-zero forced set with the old bottom cap deleted",
            "replacement": "old bottom cap reinserted unchanged plus straight runs on the outer L",
            "attachment_rule": "each outer run has at most one attachment to the old rooted tree",
            "scope": "all three-site masks; no inner frame vertices",
        },
        "symbolic_obstruction": {
            "required_replacement": "7k+1",
            "outer_arm_capacity": "3k+5",
            "fixed_hub_grammar_capacity": "6k+4",
            "deficit": "k-3",
            "successor_required_gain": 7,
            "successor_grammar_gain": 6,
        },
        "records": records,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--stdout", action="store_true")
    args = parser.parse_args()
    payload = json.dumps(build_report(), indent=2, sort_keys=True) + "\n"
    if args.stdout:
        print(payload, end="")
    else:
        args.output.write_text(payload)


if __name__ == "__main__":
    main()
