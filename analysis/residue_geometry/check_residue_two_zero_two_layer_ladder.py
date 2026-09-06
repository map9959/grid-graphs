#!/usr/bin/env python3
"""Exhaust the declared two-layer residue-zero terminal ladder grammar."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import json
from pathlib import Path
from typing import Iterator

from analysis.patterns.diagonal_patterns import residue_zero_phase_pattern
from analysis.residue_geometry.check_residue_two_zero_cap_exchange import (
    Edge,
    Vertex,
    _components,
    _interval_incidence,
    _is_acyclic,
    _star,
    _straight,
    _unit_cell_violations,
)
from analysis._paths import analysis_path


SCHEMA = "grid-graphs.residue-two-zero-two-layer-ladder.v1"
DEFAULT_OUTPUT = analysis_path("residue_two_zero_two_layer_ladder.json")
ORIENTATIONS = ("identity", "transpose", "rotate180", "anti_transpose")


@dataclass(frozen=True)
class PacketDescriptor:
    orientation: str
    bottom_mask: int
    right_mask: int
    rung_offset: int | None
    cap_mask: int

    @property
    def packet_gain(self) -> int:
        return (
            self.bottom_mask.bit_count()
            + self.right_mask.bit_count()
            + int(self.rung_offset is not None)
        )


def iter_descriptors() -> Iterator[PacketDescriptor]:
    for orientation in ORIENTATIONS:
        for bottom_mask in range(8):
            for right_mask in range(8):
                for rung_state in range(4):
                    rung_offset = None if rung_state == 0 else rung_state - 1
                    for cap_mask in range(4):
                        yield PacketDescriptor(
                            orientation, bottom_mask, right_mask, rung_offset, cap_mask
                        )


def _transform(vertex: Vertex, n: int, orientation: str) -> Vertex:
    row, column = vertex
    if orientation == "identity":
        return vertex
    if orientation == "transpose":
        return column, row
    if orientation == "rotate180":
        return n - 1 - row, n - 1 - column
    if orientation == "anti_transpose":
        return n - 1 - column, n - 1 - row
    raise ValueError(f"unknown orientation {orientation}")


def _source_sets(k: int) -> tuple[int, int, set[Vertex], set[Vertex], set[Vertex]]:
    old_n, n = 3 * k, 3 * k + 2
    rows = residue_zero_phase_pattern(old_n)
    source = {
        (row, column)
        for row, values in enumerate(rows)
        for column, value in enumerate(values)
        if value == "."
    }
    deleted_cap = {(old_n - 1, column) for column in range(old_n) if column != 1}
    return old_n, n, source, deleted_cap, source - deleted_cap


def materialize(descriptor: PacketDescriptor, k: int) -> tuple[set[Vertex], set[Vertex]]:
    """Return transformed retained and complete forced sets."""
    old_n, n, _, _, retained = _source_sets(k)
    replacement: set[Vertex] = set()
    for packet in range(k):
        for offset in range(3):
            if descriptor.bottom_mask & (1 << offset):
                replacement.add((old_n + 1, 3 * packet + offset))
            if descriptor.right_mask & (1 << offset):
                replacement.add((3 * packet + offset, old_n + 1))
        if descriptor.rung_offset is not None:
            replacement.add((old_n - 1, 3 * packet + descriptor.rung_offset))
    cap_vertices = (
        (old_n, old_n),
        (old_n, old_n + 1),
        (old_n + 1, old_n),
        (old_n + 1, old_n + 1),
    )
    replacement.add(cap_vertices[descriptor.cap_mask])
    transformed_retained = {
        _transform(vertex, n, descriptor.orientation) for vertex in retained
    }
    transformed_replacement = {
        _transform(vertex, n, descriptor.orientation) for vertex in replacement
    }
    return transformed_retained, transformed_retained | transformed_replacement


def _cycle_rank(edges: frozenset[Edge]) -> int:
    vertices = {vertex for edge in edges for vertex in edge}
    adjacency = {vertex: [] for vertex in vertices}
    for left, right in edges:
        adjacency[left].append(right)
        adjacency[right].append(left)
    remaining = set(vertices)
    components = 0
    while remaining:
        components += 1
        pending = [remaining.pop()]
        while pending:
            for neighbor in adjacency[pending.pop()]:
                if neighbor in remaining:
                    remaining.remove(neighbor)
                    pending.append(neighbor)
    return len(edges) - len(vertices) + components


def evaluate(descriptor: PacketDescriptor, k: int) -> dict:
    old_n, n, _, _, _ = _source_sets(k)
    retained, forced = materialize(descriptor, k)
    components = _components(forced, n)
    stars = [_star(component, n) for component in components]
    edges = frozenset().union(*(star_edges for star_edges, _ in stars))
    links, maximum_intersection, connected = _interval_incidence(components, n)

    # This is the obstruction pair before applying the grid isometry.
    rows = residue_zero_phase_pattern(old_n)
    source = {
        (row, column)
        for row, values in enumerate(rows)
        for column, value in enumerate(values)
        if value == "."
    }
    deleted = {(old_n - 1, column) for column in range(old_n) if column != 1}
    identity_retained = source - deleted
    right_component = next(
        component
        for component in _components(identity_retained, n)
        if (2, old_n - 1) in component
    )
    right_rail = frozenset((row, old_n + 1) for row in range(old_n))
    parallel_intersection = len(_star(right_component, n)[1] & _star(right_rail, n)[1])

    target = 3 * k * k + 7 * k
    checks = {
        "exact_target_count": len(forced) == target,
        "unit_cells_valid": not _unit_cell_violations(forced, n),
        "components_straight": all(map(_straight, components)),
        "singleton_star_intersections": maximum_intersection <= 1,
        "tree_incidence": connected
        and maximum_intersection <= 1
        and links == len(components) - 1,
        "forced_forest": _is_acyclic(edges),
        "stable_packet_gain_seven": descriptor.packet_gain == 7,
    }
    return {
        "descriptor": {
            "orientation": descriptor.orientation,
            "bottom_mask": f"{descriptor.bottom_mask:03b}",
            "right_mask": f"{descriptor.right_mask:03b}",
            "rung_offset": descriptor.rung_offset,
            "cap_mask": descriptor.cap_mask,
        },
        "k": k,
        "n": n,
        "forced_count": len(forced),
        "target_count": target,
        "component_count": len(components),
        "incidence_links": links,
        "incidence_connected": connected,
        "maximum_star_intersection": maximum_intersection,
        "parallel_right_rail_intersection": parallel_intersection,
        "forced_cycle_rank": _cycle_rank(edges),
        "checks": checks,
        "survives": all(checks.values()),
    }


def analyze_k(k: int) -> dict:
    if k < 7:
        raise ValueError("the residue-zero phase source requires k >= 7")
    descriptors = list(iter_descriptors())
    exact = [descriptor for descriptor in descriptors if descriptor.packet_gain == 7]
    evaluations = [evaluate(descriptor, k) for descriptor in exact]
    best = min(
        evaluations,
        key=lambda item: (
            item["forced_cycle_rank"],
            item["maximum_star_intersection"],
            item["descriptor"]["orientation"],
            item["descriptor"]["rung_offset"],
            item["descriptor"]["cap_mask"],
        ),
    )
    checks = {
        "declared_descriptor_count": len(descriptors) == 4096,
        "exact_descriptor_count": len(exact) == 48,
        "exact_masks_are_saturated": all(
            descriptor.bottom_mask == 7
            and descriptor.right_mask == 7
            and descriptor.rung_offset is not None
            for descriptor in exact
        ),
        "all_exact_counts_match_target": all(
            item["checks"]["exact_target_count"] for item in evaluations
        ),
        "all_exact_unit_cells_valid": all(
            item["checks"]["unit_cells_valid"] for item in evaluations
        ),
        "all_exact_components_straight": all(
            item["checks"]["components_straight"] for item in evaluations
        ),
        "parallel_intersection_formula": all(
            item["parallel_right_rail_intersection"] == 3 * k - 5
            for item in evaluations
        ),
        "no_singleton_intersection_candidate": all(
            not item["checks"]["singleton_star_intersections"] for item in evaluations
        ),
        "no_tree_incidence_candidate": all(
            not item["checks"]["tree_incidence"] for item in evaluations
        ),
        "no_forced_forest_candidate": all(
            not item["checks"]["forced_forest"] for item in evaluations
        ),
        "best_cycle_rank_formula": best["forced_cycle_rank"] == 3 * k - 5,
    }
    return {
        "k": k,
        "n": 3 * k + 2,
        "status": "complete_grammar_obstruction" if all(checks.values()) else "claim_mismatch",
        "enumeration": {
            "orientations": len(ORIENTATIONS),
            "bottom_masks": 8,
            "right_masks": 8,
            "rung_states": 4,
            "cap_masks": 4,
            "declared_descriptors": len(descriptors),
            "exact_count_descriptors": len(exact),
            "materializations_checked": len(evaluations),
        },
        "obstruction": {
            "forced_exact_packet": "bottom=111, right=111, one rung",
            "parallel_right_rail_intersection": 3 * k - 5,
            "minimum_forced_cycle_rank": best["forced_cycle_rank"],
            "survivors": sum(item["survives"] for item in evaluations),
        },
        "best_exact_materialization": best,
        "checks": checks,
    }


def build_report(ks: tuple[int, ...] = (7, 8, 9)) -> dict:
    records = [analyze_k(k) for k in ks]
    return {
        "schema": SCHEMA,
        "checker": "residue_two_zero_two_layer_ladder",
        "status": "complete_grammar_obstruction"
        if all(record["status"] == "complete_grammar_obstruction" for record in records)
        else "claim_mismatch",
        "k_values": list(ks),
        "grammar": {
            "packet_sites": "three outer-bottom rail, three outer-right rail, one old-bottom rung",
            "packet_masks": "8 bottom masks x 8 right masks x 4 rung states",
            "cap_masks": "one forced vertex at one of four terminal 2x2 coordinates",
            "orientations": list(ORIENTATIONS),
            "hard_descriptor_bound": 4096,
            "exact_descriptor_bound": 48,
        },
        "symbolic_obstruction": {
            "replacement_count": "7k+1",
            "successor_packet_gain": 7,
            "forced_packet": "111/111 plus one rung",
            "right_rail_star_intersection": "3k-5",
            "minimum_cycle_rank": "3k-5",
        },
        "next_topology": {
            "name": "double-cap two-layer interval ladder",
            "additional_deletion": "rightmost retained interval, length 3k-5",
            "replacement_count": "10k-4",
            "successor_packet_gain": 10,
            "packet": "three bottom rail + three right rail + bottom rung + right rung + two pivot-separated inner connectors",
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
