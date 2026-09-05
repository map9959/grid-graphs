#!/usr/bin/env python3
"""Check the phase-alternating twelve-site sparse-rail ladder grammar."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import json
from pathlib import Path
from typing import Iterator

from check_residue_two_zero_cap_exchange import (
    _components,
    _interval_incidence,
    _is_acyclic,
    _star,
    _straight,
    _unit_cell_violations,
)
from check_residue_two_zero_double_cap_exchange import (
    _cap_vertices,
    _cycle_rank,
    _source_sets,
)
from check_residue_two_zero_two_layer_ladder import ORIENTATIONS, _transform


SCHEMA = "grid-graphs.residue-two-zero-sparse-rail-ladder.v1"
DEFAULT_OUTPUT = Path(__file__).with_name("residue_two_zero_sparse_rail_ladder.json")
DIRECTIONS = (-1, 1)
HARD_DESCRIPTOR_BOUND = len(ORIENTATIONS) * 3 * 3 * 2 * 2 * 4


@dataclass(frozen=True)
class SparseRailDescriptor:
    orientation: str
    bottom_phase: int
    right_phase: int
    bottom_direction: int
    right_direction: int
    cap_mask: int


def iter_descriptors() -> Iterator[SparseRailDescriptor]:
    for orientation in ORIENTATIONS:
        for bottom_phase in range(3):
            for right_phase in range(3):
                for bottom_direction in DIRECTIONS:
                    for right_direction in DIRECTIONS:
                        for cap_mask in range(4):
                            yield SparseRailDescriptor(
                                orientation,
                                bottom_phase,
                                right_phase,
                                bottom_direction,
                                right_direction,
                                cap_mask,
                            )


def materialize(
    descriptor: SparseRailDescriptor, k: int
) -> tuple[set[tuple[int, int]], set[tuple[int, int]], set[tuple[int, int]]]:
    old_n, n, _, _, _, retained = _source_sets(k)
    replacement: set[tuple[int, int]] = set()
    for packet in range(k - 2):
        start = 2 + 3 * packet
        bottom_gap = (
            descriptor.bottom_phase + descriptor.bottom_direction * packet
        ) % 3
        right_gap = (
            descriptor.right_phase + descriptor.right_direction * packet
        ) % 3

        # Per arm: two sparse-rail sites, two complementary old-layer sites,
        # and one connector at the rail gap on the new inner layer.
        replacement.update(
            (old_n + 1, start + offset)
            for offset in range(3)
            if offset != bottom_gap
        )
        replacement.update(
            (old_n - 1, start + offset)
            for offset in range(3)
            if offset != bottom_gap
        )
        replacement.add((old_n, start + bottom_gap))

        replacement.update(
            (start + offset, old_n + 1)
            for offset in range(3)
            if offset != right_gap
        )
        replacement.update(
            (start + offset, old_n - 1)
            for offset in range(3)
            if offset != right_gap
        )
        replacement.add((start + right_gap, old_n))

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


def evaluate(descriptor: SparseRailDescriptor, k: int) -> dict:
    _, n, _, _, _, retained_source = _source_sets(k)
    retained, replacement, forced = materialize(descriptor, k)
    components = _components(forced, n)
    stars = [_star(component, n) for component in components]
    edges = frozenset().union(*(star_edges for star_edges, _ in stars))
    links, maximum_intersection, connected = _interval_incidence(components, n)
    target = 3 * k * k + 7 * k
    unit_violations = _unit_cell_violations(forced, n)
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
        "stable_count_interface": len(replacement) == 10 * (k - 2) + 16,
    }
    return {
        "descriptor": {
            "orientation": descriptor.orientation,
            "bottom_phase": descriptor.bottom_phase,
            "right_phase": descriptor.right_phase,
            "bottom_direction": descriptor.bottom_direction,
            "right_direction": descriptor.right_direction,
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
    descriptors = list(iter_descriptors())
    evaluations = [evaluate(descriptor, k) for descriptor in descriptors]
    best = min(
        evaluations,
        key=lambda item: (
            item["maximum_star_intersection"],
            item["forced_cycle_rank"],
            item["descriptor"]["orientation"],
            item["descriptor"]["cap_mask"],
        ),
    )
    minimum_cycle_rank = min(item["forced_cycle_rank"] for item in evaluations)
    checks = {
        "hard_descriptor_bound": HARD_DESCRIPTOR_BOUND == 576,
        "all_descriptors_enumerated": len(descriptors) == HARD_DESCRIPTOR_BOUND,
        "all_replacement_counts_exact": all(
            item["checks"]["replacement_count"] for item in evaluations
        ),
        "all_target_counts_exact": all(
            item["checks"]["exact_target_count"] for item in evaluations
        ),
        "all_unit_cells_valid": all(
            item["checks"]["unit_cells_valid"] for item in evaluations
        ),
        "all_components_straight": all(
            item["checks"]["components_straight"] for item in evaluations
        ),
        "minimum_intersection_is_three": min(
            item["maximum_star_intersection"] for item in evaluations
        ) == 3,
        "no_singleton_intersection_candidate": all(
            not item["checks"]["singleton_star_intersections"]
            for item in evaluations
        ),
        "no_incidence_tree_candidate": all(
            not item["checks"]["incidence_tree"] for item in evaluations
        ),
        "no_forced_forest_candidate": all(
            not item["checks"]["forced_forest"] for item in evaluations
        ),
        "all_count_interfaces_stable": all(
            item["checks"]["stable_count_interface"] for item in evaluations
        ),
    }
    return {
        "k": k,
        "n": 3 * k + 2,
        "status": "complete_grammar_obstruction" if all(checks.values()) else "claim_mismatch",
        "enumeration": {
            "orientations": len(ORIENTATIONS),
            "bottom_phases": 3,
            "right_phases": 3,
            "bottom_directions": 2,
            "right_directions": 2,
            "cap_masks": 4,
            "hard_descriptor_bound": HARD_DESCRIPTOR_BOUND,
            "materializations_checked": len(evaluations),
        },
        "obstruction": {
            "minimum_star_intersection": 3,
            "minimum_forced_cycle_rank": minimum_cycle_rank,
            "survivors": sum(item["survives"] for item in evaluations),
            "track_capacity": "three auxiliary vertices per arm occupy two inner tracks",
        },
        "best_materialization": best,
        "checks": checks,
    }


def build_report(ks: tuple[int, ...] = (7, 8, 9)) -> dict:
    records = [analyze_k(k) for k in ks]
    return {
        "schema": SCHEMA,
        "checker": "residue_two_zero_sparse_rail_ladder",
        "status": "complete_grammar_obstruction"
        if all(record["status"] == "complete_grammar_obstruction" for record in records)
        else "claim_mismatch",
        "k_values": list(ks),
        "grammar": {
            "packet_count": "k-2",
            "packet_capacity": 12,
            "packet_gain": 10,
            "outer_masks": "omit phase gap; select complementary two positions",
            "old_layer_masks": "select the same complementary two positions",
            "connector_masks": "select the phase-gap position on the new inner layer",
            "phase_recurrence": "gap(t+1)=gap(t)+direction mod 3",
            "cap": "one of four sixteen-vertex caps",
            "hard_descriptor_bound": HARD_DESCRIPTOR_BOUND,
        },
        "symbolic_obstruction": {
            "minimum_star_intersection": 3,
            "reason": "the outer and old-layer complementary masks create parallel runs while the gap connector adds a third competing attachment",
            "stable_count_gain": 10,
            "stable_topology": False,
        },
        "branch_decision": {
            "continue_fixed_two_layer_zero_cap_splice": False,
            "reason": "three successive exact grammars fail by linear-density parallel-star intersections; adding bounded leaves only moves the collision between two tracks",
            "only_justified_relaxation": "a three-layer moving-seam exchange or deletion of another old interval, neither of which is a neighboring-residue two-frame cap splice",
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
