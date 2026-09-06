#!/usr/bin/env python3
"""Exhaust the declared ten-site residue-zero double-cap exchange grammar."""

from __future__ import annotations

import argparse
import itertools
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Iterator

from analysis._paths import analysis_path
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
from analysis.residue_geometry.check_residue_two_zero_two_layer_ladder import (
    ORIENTATIONS,
    _transform,
)

SCHEMA = "grid-graphs.residue-two-zero-double-cap-exchange.v1"
DEFAULT_OUTPUT = analysis_path("residue_two_zero_double_cap_exchange.json")
RAW_PACKET_DESCRIPTORS = 8 * 8 * 4**4
RAW_CAP_MASKS = 4
RAW_DESCRIPTOR_BOUND = len(ORIENTATIONS) * RAW_PACKET_DESCRIPTORS * RAW_CAP_MASKS


@dataclass(frozen=True)
class DoubleCapDescriptor:
    orientation: str
    bottom_rail_mask: int
    right_rail_mask: int
    bottom_rung: int | None
    right_rung: int | None
    bottom_connector: int | None
    right_connector: int | None
    cap_mask: int

    @property
    def packet_gain(self) -> int:
        bottom_aux = {x for x in (self.bottom_rung, self.bottom_connector) if x is not None}
        right_aux = {x for x in (self.right_rung, self.right_connector) if x is not None}
        return (
            self.bottom_rail_mask.bit_count()
            + self.right_rail_mask.bit_count()
            + len(bottom_aux)
            + len(right_aux)
        )

    @property
    def cap_gain(self) -> int:
        return 16


def iter_exact_descriptors() -> Iterator[DoubleCapDescriptor]:
    """Enumerate exactly the descriptors capable of count 10k-4 for k>=7."""
    for orientation in ORIENTATIONS:
        for bottom_rung, bottom_connector in itertools.permutations(range(3), 2):
            for right_rung, right_connector in itertools.permutations(range(3), 2):
                for cap_mask in range(4):
                    yield DoubleCapDescriptor(
                        orientation=orientation,
                        bottom_rail_mask=7,
                        right_rail_mask=7,
                        bottom_rung=bottom_rung,
                        right_rung=right_rung,
                        bottom_connector=bottom_connector,
                        right_connector=right_connector,
                        cap_mask=cap_mask,
                    )


def _source_sets(
    k: int,
) -> tuple[int, int, set[Vertex], set[Vertex], set[Vertex], set[Vertex]]:
    old_n, n = 3 * k, 3 * k + 2
    rows = residue_zero_phase_pattern(old_n)
    source = {
        (row, column)
        for row, values in enumerate(rows)
        for column, value in enumerate(values)
        if value == "."
    }
    bottom_cap = {(old_n - 1, column) for column in range(old_n) if column != 1}
    right_interval = {
        (row, old_n - 1) for row in range(2, old_n - 3)
    }
    retained = source - bottom_cap - right_interval
    return old_n, n, source, bottom_cap, right_interval, retained


def _cap_vertices(old_n: int, cap_mask: int) -> set[Vertex]:
    rail_coordinates = (0, 1, old_n - 4, old_n - 3, old_n - 2, old_n - 1)
    fixed = {
        *((old_n + 1, column) for column in rail_coordinates),
        *((row, old_n + 1) for row in rail_coordinates),
        (old_n - 1, 0),
        (old_n - 1, old_n - 4),
        (old_n - 4, old_n - 1),
    }
    corner_choices = (
        (old_n, old_n),
        (old_n, old_n + 1),
        (old_n + 1, old_n),
        (old_n + 1, old_n + 1),
    )
    fixed.add(corner_choices[cap_mask])
    return fixed


def materialize(
    descriptor: DoubleCapDescriptor, k: int
) -> tuple[set[Vertex], set[Vertex], set[Vertex]]:
    old_n, n, _, _, _, retained = _source_sets(k)
    replacement: set[Vertex] = set()
    for packet in range(k - 2):
        start = 2 + 3 * packet
        for offset in range(3):
            if descriptor.bottom_rail_mask & (1 << offset):
                replacement.add((old_n + 1, start + offset))
            if descriptor.right_rail_mask & (1 << offset):
                replacement.add((start + offset, old_n + 1))
        for offset in {descriptor.bottom_rung, descriptor.bottom_connector} - {None}:
            replacement.add((old_n - 1, start + offset))
        for offset in {descriptor.right_rung, descriptor.right_connector} - {None}:
            replacement.add((start + offset, old_n - 1))
    replacement.update(_cap_vertices(old_n, descriptor.cap_mask))
    transformed_retained = {
        _transform(vertex, n, descriptor.orientation) for vertex in retained
    }
    transformed_replacement = {
        _transform(vertex, n, descriptor.orientation) for vertex in replacement
    }
    return (
        transformed_retained,
        transformed_replacement,
        transformed_retained | transformed_replacement,
    )


def _cycle_rank(edges: frozenset[Edge]) -> int:
    vertices = {vertex for edge in edges for vertex in edge}
    adjacency = {vertex: [] for vertex in vertices}
    for left, right in edges:
        adjacency[left].append(right)
        adjacency[right].append(left)
    remaining = set(vertices)
    component_count = 0
    while remaining:
        component_count += 1
        pending = [remaining.pop()]
        while pending:
            for neighbor in adjacency[pending.pop()]:
                if neighbor in remaining:
                    remaining.remove(neighbor)
                    pending.append(neighbor)
    return len(edges) - len(vertices) + component_count


def evaluate(descriptor: DoubleCapDescriptor, k: int) -> dict:
    _, n, _, _, _, retained_source = _source_sets(k)
    retained, replacement, forced = materialize(descriptor, k)
    components = _components(forced, n)
    stars = [_star(component, n) for component in components]
    edges = frozenset().union(*(star_edges for star_edges, _ in stars))
    links, maximum_intersection, connected = _interval_incidence(components, n)
    unit_violations = _unit_cell_violations(forced, n)
    target = 3 * k * k + 7 * k
    checks = {
        "retained_count": len(retained_source) == 3 * k * k - 3 * k + 4,
        "replacement_count": len(replacement) == 10 * k - 4,
        "exact_target_count": len(forced) == target,
        "unit_cells_valid": not unit_violations,
        "components_straight": all(map(_straight, components)),
        "singleton_star_intersections": maximum_intersection <= 1,
        "incidence_tree": connected
        and maximum_intersection <= 1
        and links == len(components) - 1,
        "forced_forest": _is_acyclic(edges),
        "stable_packet_gain_ten": descriptor.packet_gain == 10,
        "cap_gain_sixteen": descriptor.cap_gain == 16,
    }
    return {
        "descriptor": {
            "orientation": descriptor.orientation,
            "bottom_rail_mask": f"{descriptor.bottom_rail_mask:03b}",
            "right_rail_mask": f"{descriptor.right_rail_mask:03b}",
            "bottom_rung": descriptor.bottom_rung,
            "right_rung": descriptor.right_rung,
            "bottom_connector": descriptor.bottom_connector,
            "right_connector": descriptor.right_connector,
            "cap_mask": descriptor.cap_mask,
        },
        "k": k,
        "n": n,
        "replacement_count": len(replacement),
        "forced_count": len(forced),
        "target_count": target,
        "unit_cell_violation_count": len(unit_violations),
        "component_count": len(components),
        "incidence_links": links,
        "incidence_connected": connected,
        "maximum_star_intersection": maximum_intersection,
        "forced_cycle_rank": _cycle_rank(edges),
        "checks": checks,
        "survives": all(checks.values()),
    }


def analyze_k(k: int) -> dict:
    if k < 7:
        raise ValueError("the residue-zero phase source requires k >= 7")
    exact_descriptors = list(iter_exact_descriptors())
    evaluations = [evaluate(descriptor, k) for descriptor in exact_descriptors]
    locally_valid = [
        item
        for item in evaluations
        if item["checks"]["unit_cells_valid"]
        and item["checks"]["components_straight"]
    ]
    best = min(
        locally_valid,
        key=lambda item: (
            item["forced_cycle_rank"],
            item["maximum_star_intersection"],
            item["descriptor"]["orientation"],
            item["descriptor"]["cap_mask"],
        ),
    )
    checks = {
        "raw_descriptor_bound": RAW_DESCRIPTOR_BOUND == 262_144,
        "exact_descriptor_count": len(exact_descriptors) == 576,
        "all_exact_packet_gains": all(
            descriptor.packet_gain == 10 for descriptor in exact_descriptors
        ),
        "all_exact_cap_gains": all(
            descriptor.cap_gain == 16 for descriptor in exact_descriptors
        ),
        "all_exact_counts": all(
            item["checks"]["exact_target_count"] for item in evaluations
        ),
        "local_survivor_count": len(locally_valid) == 576,
        "no_singleton_intersection_candidate": all(
            not item["checks"]["singleton_star_intersections"]
            for item in locally_valid
        ),
        "no_incidence_tree_candidate": all(
            not item["checks"]["incidence_tree"] for item in evaluations
        ),
        "no_forced_forest_candidate": all(
            not item["checks"]["forced_forest"] for item in evaluations
        ),
        "minimum_intersection_is_two": min(
            item["maximum_star_intersection"] for item in locally_valid
        ) == 2,
        "minimum_cycle_rank_formula": best["forced_cycle_rank"] == 4 * k - 8,
    }
    return {
        "k": k,
        "n": 3 * k + 2,
        "status": "complete_grammar_obstruction" if all(checks.values()) else "claim_mismatch",
        "enumeration": {
            "raw_packet_descriptors": RAW_PACKET_DESCRIPTORS,
            "raw_cap_masks": RAW_CAP_MASKS,
            "orientations": len(ORIENTATIONS),
            "hard_raw_descriptor_bound": RAW_DESCRIPTOR_BOUND,
            "exact_descriptors": len(exact_descriptors),
            "locally_valid_descriptors": len(locally_valid),
            "materializations_checked": len(evaluations),
        },
        "obstruction": {
            "exact_packet": "111 bottom rail, 111 right rail, two distinct bottom offsets, two distinct right offsets",
            "periodic_density": "every repeated two-of-three auxiliary mask has an adjacent pair",
            "minimum_star_intersection": 2,
            "minimum_forced_cycle_rank": best["forced_cycle_rank"],
            "survivors": sum(item["survives"] for item in evaluations),
        },
        "best_local_materialization": best,
        "checks": checks,
    }


def build_report(ks: tuple[int, ...] = (7, 8, 9)) -> dict:
    records = [analyze_k(k) for k in ks]
    return {
        "schema": SCHEMA,
        "checker": "residue_two_zero_double_cap_exchange",
        "status": "complete_grammar_obstruction"
        if all(record["status"] == "complete_grammar_obstruction" for record in records)
        else "claim_mismatch",
        "k_values": list(ks),
        "grammar": {
            "packets": "k-2 repeated ten-site packets",
            "packet": "three cells on each outer rail plus two distinct auxiliary offsets on each deleted cap layer",
            "cap": "one of four fixed sixteen-vertex terminal caps",
            "replacement_formula": "10(k-2)+16=10k-4",
            "raw_descriptor_bound": RAW_DESCRIPTOR_BOUND,
            "exact_descriptor_count": 576,
        },
        "symbolic_obstruction": {
            "forced_auxiliary_density": "two of every three positions on both arms",
            "adjacent_pair": "inside each packet or across each packet boundary",
            "star_intersection": "at least two with the saturated parallel outer rail",
            "minimum_cycle_rank": "4k-8",
        },
        "next_topology": {
            "name": "phase-alternating twelve-site sparse-rail ladder",
            "packet_capacity": 12,
            "packet_gain": 10,
            "rule": "omit one site from each outer rail and replace both by pivot-separated reservoir leaves",
            "phase": "move each rail gap across packet boundaries so auxiliary components remain singleton",
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
