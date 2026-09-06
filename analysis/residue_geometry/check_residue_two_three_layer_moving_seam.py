#!/usr/bin/env python3
"""Check a genuine three-inner-track moving-seam interval grammar."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import itertools
import json
from pathlib import Path
from typing import Iterator

from analysis.residue_geometry.check_residue_two_zero_cap_exchange import (
    _components,
    _interval_incidence,
    _is_acyclic,
    _star,
    _straight,
    _unit_cell_violations,
)
from analysis.residue_geometry.check_residue_two_zero_double_cap_exchange import (
    _cap_vertices,
    _cycle_rank,
    _source_sets,
)
from analysis._paths import analysis_path


SCHEMA = "grid-graphs.residue-two-three-layer-moving-seam.v1"
DEFAULT_OUTPUT = analysis_path("residue_two_three_layer_moving_seam.json")
DIRECTIONS = (-1, 1)
TRACK_PHASES = tuple(itertools.product(range(3), repeat=3))
ARM_WORDS = 3 * len(DIRECTIONS) * len(TRACK_PHASES)
HARD_DESCRIPTOR_BOUND = ARM_WORDS * ARM_WORDS * 4


@dataclass(frozen=True)
class ArmWord:
    phase: int
    direction: int
    track_phases: tuple[int, int, int]


@dataclass(frozen=True)
class MovingSeamDescriptor:
    bottom: ArmWord
    right: ArmWord
    cap_mask: int


def derive_count_ledger(k: int) -> dict:
    """Derive the forced packet gain and cap count without enumeration."""
    if k < 7:
        raise ValueError("the residue-zero phase source requires k >= 7")
    retained = 3 * k * k - 3 * k + 4
    target = 3 * k * k + 7 * k
    replacement = target - retained
    packet_count = k - 2
    cap_count = 16
    numerator = replacement - cap_count
    if numerator % packet_count:
        raise AssertionError("the declared cap does not induce an integral packet gain")
    packet_gain = numerator // packet_count
    if packet_gain != 10 or replacement != 10 * k - 4:
        raise AssertionError("unexpected residue-two count ledger")
    return {
        "retained_count": retained,
        "target_count": target,
        "replacement_count": replacement,
        "packet_count": packet_count,
        "packet_gain": packet_gain,
        "cap_count": cap_count,
        "identity": "10(k-2)+16=10k-4",
    }


def iter_arm_words() -> Iterator[ArmWord]:
    for phase in range(3):
        for direction in DIRECTIONS:
            for track_phases in TRACK_PHASES:
                yield ArmWord(phase, direction, track_phases)


def iter_descriptors() -> Iterator[MovingSeamDescriptor]:
    words = tuple(iter_arm_words())
    for bottom in words:
        for right in words:
            for cap_mask in range(4):
                yield MovingSeamDescriptor(bottom, right, cap_mask)


def _arm_vertices(word: ArmWord, packet: int) -> set[tuple[int, int]]:
    seam = (word.phase + word.direction * packet) % 3
    return {
        *((3, offset) for offset in range(3) if offset != seam),
        *((track, (seam + shift) % 3) for track, shift in enumerate(word.track_phases)),
    }


def materialize(
    descriptor: MovingSeamDescriptor, k: int
) -> tuple[set[tuple[int, int]], set[tuple[int, int]], set[tuple[int, int]]]:
    old_n, _, _, _, _, retained = _source_sets(k)
    replacement: set[tuple[int, int]] = set()
    for packet in range(k - 2):
        start = 2 + 3 * packet
        for track, offset in _arm_vertices(descriptor.bottom, packet):
            replacement.add((old_n - 2 + track, start + offset))
        for track, offset in _arm_vertices(descriptor.right, packet):
            replacement.add((start + offset, old_n - 2 + track))
    replacement.update(_cap_vertices(old_n, descriptor.cap_mask))
    return retained, replacement, retained | replacement


def _word_dict(word: ArmWord) -> dict:
    return {
        "phase": word.phase,
        "direction": word.direction,
        "track_phases": list(word.track_phases),
    }


def evaluate(descriptor: MovingSeamDescriptor, k: int) -> dict:
    ledger = derive_count_ledger(k)
    _, n, _, _, _, retained_source = _source_sets(k)
    retained, replacement, forced = materialize(descriptor, k)
    components = _components(forced, n)
    stars = [_star(component, n) for component in components]
    edges = frozenset().union(*(star_edges for star_edges, _ in stars))
    links, maximum_intersection, connected = _interval_incidence(components, n)
    unit_violations = _unit_cell_violations(forced, n)
    checks = {
        "retained_count": len(retained_source) == ledger["retained_count"],
        "replacement_count": len(replacement) == ledger["replacement_count"],
        "exact_target_count": len(forced) == ledger["target_count"],
        "unit_cells_valid": not unit_violations,
        "components_straight": all(map(_straight, components)),
        "singleton_star_intersections": maximum_intersection <= 1,
        "incidence_tree": connected
        and maximum_intersection <= 1
        and links == len(components) - 1,
        "forced_forest": _is_acyclic(edges),
        "stable_packet_gain_ten": ledger["packet_gain"] == 10,
        "cap_count_sixteen": ledger["cap_count"] == 16,
    }
    return {
        "descriptor": {
            "bottom": _word_dict(descriptor.bottom),
            "right": _word_dict(descriptor.right),
            "cap_mask": descriptor.cap_mask,
        },
        "k": k,
        "n": n,
        "replacement_count": len(replacement),
        "forced_count": len(forced),
        "target_count": ledger["target_count"],
        "unit_cell_violation_count": len(unit_violations),
        "component_count": len(components),
        "incidence_links": links,
        "incidence_connected": connected,
        "maximum_star_intersection": maximum_intersection,
        "forced_cycle_rank": _cycle_rank(edges),
        "checks": checks,
        "survives": all(checks.values()),
    }


def _strip_admissible(word: ArmWord, k: int, axis: str) -> bool:
    """Apply the monotone unit-cell gate to one arm independently."""
    old_n, n, _, _, _, retained = _source_sets(k)
    replacement: set[tuple[int, int]] = set()
    for packet in range(k - 2):
        start = 2 + 3 * packet
        for track, offset in _arm_vertices(word, packet):
            vertex = (old_n - 2 + track, start + offset)
            replacement.add(vertex if axis == "bottom" else vertex[::-1])
    forced = retained | replacement
    return not _unit_cell_violations(forced, n)


def analyze_k(k: int) -> dict:
    ledger = derive_count_ledger(k)
    words = tuple(iter_arm_words())
    bottom_words = tuple(word for word in words if _strip_admissible(word, k, "bottom"))
    right_words = tuple(word for word in words if _strip_admissible(word, k, "right"))
    descriptors = (
        MovingSeamDescriptor(bottom, right, cap_mask)
        for bottom in bottom_words
        for right in right_words
        for cap_mask in range(4)
    )
    evaluations = [evaluate(descriptor, k) for descriptor in descriptors]
    best = min(
        evaluations,
        key=lambda item: (
            item["unit_cell_violation_count"],
            not item["checks"]["components_straight"],
            item["maximum_star_intersection"],
            item["forced_cycle_rank"],
            json.dumps(item["descriptor"], sort_keys=True),
        ),
    )
    survivors = [item for item in evaluations if item["survives"]]
    local = [
        item
        for item in evaluations
        if item["checks"]["unit_cells_valid"]
        and item["checks"]["components_straight"]
    ]
    return {
        "k": k,
        "n": 3 * k + 2,
        "status": "candidate_found" if survivors else "complete_grammar_obstruction",
        "count_ledger": ledger,
        "enumeration": {
            "arm_words": ARM_WORDS,
            "cap_masks": 4,
            "hard_descriptor_bound": HARD_DESCRIPTOR_BOUND,
            "descriptors_classified": HARD_DESCRIPTOR_BOUND,
            "bottom_strip_admissible": len(bottom_words),
            "right_strip_admissible": len(right_words),
            "joint_materializations_checked": len(evaluations),
            "locally_valid": len(local),
        },
        "capacity_or_intersection": {
            "packet_capacity": 24,
            "packet_gain": 10,
            "minimum_unit_cell_violations": min(
                item["unit_cell_violation_count"] for item in evaluations
            ),
            "minimum_star_intersection_among_local": min(
                (item["maximum_star_intersection"] for item in local), default=None
            ),
            "minimum_cycle_rank_among_local": min(
                (item["forced_cycle_rank"] for item in local), default=None
            ),
            "survivors": len(survivors),
        },
        "best_materialization": best,
        "first_survivor": survivors[0] if survivors else None,
    }


def build_report(ks: tuple[int, ...] = (7, 8, 9)) -> dict:
    ledgers = [derive_count_ledger(k) for k in ks]
    records = [analyze_k(k) for k in ks]
    survives_all = all(record["status"] == "candidate_found" for record in records)
    return {
        "schema": SCHEMA,
        "checker": "residue_two_three_layer_moving_seam",
        "status": "candidate_found" if survives_all else "complete_grammar_obstruction",
        "algebra_before_enumeration": {
            "retained": "3k^2-3k+4",
            "target": "3k^2+7k",
            "replacement": "10k-4",
            "packet_count": "k-2",
            "cap_count": 16,
            "forced_packet_gain": 10,
            "identity": "10(k-2)+16=10k-4",
            "checked_ledgers": ledgers,
        },
        "grammar": {
            "per_arm_packet": "outer mask omits seam; one site on each of three inner tracks",
            "seam_recurrence": "s(t+1)=s(t)+d mod 3, d in {-1,+1}",
            "track_offsets": "three independent shifts in Z/3 relative to s(t)",
            "arm_words": ARM_WORDS,
            "cap_masks": 4,
            "hard_descriptor_bound": HARD_DESCRIPTOR_BOUND,
        },
        "records": records,
        "branch_assessment": {
            "stable_candidate": survives_all,
            "wholly_new_base_required": not survives_all,
            "reason": (
                "one descriptor survives every requested width"
                if survives_all
                else "the complete phase grammar has no descriptor satisfying all geometric and incidence gates"
            ),
        },
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
