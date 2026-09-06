#!/usr/bin/env python3
"""Bounded repair search for the closest rooted open-slab interfaces."""

from __future__ import annotations

import json
from itertools import combinations

from analysis.transport.census_moving_seam_alignment import d4_orientations
from analysis.patterns.construction_lab import forest_completion_check
from analysis.residue_certificates.residue_two_frontier_signatures import RankedFrontierState, replay_rows
from analysis.transport.residue_two_open_slab_census import (
    RootedOpenSlabSignature,
    mismatch,
    pattern_inputs,
    removed_prefix_cost,
)
from analysis.tiles.tile_grammar import canonicalize_partition_labels


SAMPLES = (
    ("A17", "rotate_90", "B20", "rotate_270", 2, 0, 3),
    ("A17", "rotate_180", "B20", "rotate_180_reflect_lr", 4, 2, 2),
    ("B20", "rotate_90", "A23", "rotate_270", 2, 0, 3),
)
MAX_EXCHANGE = 2


def orientation(rows: tuple[str, ...], name: str) -> tuple[str, ...]:
    return next(item.rows for item in d4_orientations(rows) if item.name == name)


def forgotten_labels(
    state: RankedFrontierState, hidden_face_slots: tuple[int, ...]
) -> tuple[int, ...]:
    """Return components represented only on the selected non-root face slots."""
    hidden = set(hidden_face_slots)
    if 0 in hidden:
        raise ValueError("OUT must remain a retained root port")
    retained_labels = {
        label for slot, label in enumerate(state.partition) if slot not in hidden
    }
    return tuple(sorted(set(state.partition) - retained_labels))


def projected_partition(
    state: RankedFrontierState, hidden_face_slots: tuple[int, ...]
) -> tuple[int, ...]:
    hidden = set(hidden_face_slots)
    return canonicalize_partition_labels(
        tuple(label for slot, label in enumerate(state.partition) if slot not in hidden)
    )


def port_set_census(
    source: RankedFrontierState,
    target: RankedFrontierState,
    slab_start: int,
) -> dict:
    """Exhaust every equal-width reroute and every one-extra-port reroute."""
    face_slots = range(1, len(target.partition))
    equal_width = [
        (
            hidden,
            forgotten_labels(target, hidden),
            projected_partition(target, hidden),
        )
        for hidden in combinations(face_slots, 3)
    ]
    one_extra = [
        (hidden, forgotten_labels(target, hidden))
        for hidden in combinations(face_slots, 2)
    ]
    closed_extra = [list(hidden) for hidden, forgotten in one_extra if not forgotten]

    straight_hidden = tuple(range(1 + slab_start, 4 + slab_start))
    straight_forgotten_labels = forgotten_labels(target, straight_hidden)
    forgotten_slots = tuple(
        slot
        for slot in straight_hidden
        if target.partition[slot] in straight_forgotten_labels
    )
    if len(forgotten_slots) != 1:
        raise AssertionError("closest sample must have one singly ported hidden component")
    extra_slot = forgotten_slots[0]
    wider_hidden = tuple(slot for slot in straight_hidden if slot != extra_slot)
    retained_slots = [
        slot for slot in range(len(target.partition)) if slot not in wider_hidden
    ]
    extra_position = retained_slots.index(extra_slot)
    wider_labels = [target.partition[slot] for slot in retained_slots]
    without_extra = canonicalize_partition_labels(
        tuple(
            label for position, label in enumerate(wider_labels) if position != extra_position
        )
    )
    return {
        "equal_width_sets_tested": len(equal_width),
        "equal_width_closed": sum(not forgotten for _, forgotten, _ in equal_width),
        "equal_width_exact": sum(
            not forgotten and projected == source.partition
            for _, forgotten, projected in equal_width
        ),
        "equal_width_minimum_forgotten": min(
            len(forgotten) for _, forgotten, _ in equal_width
        ),
        "one_extra_port_sets_tested": len(one_extra),
        "one_extra_port_closed": len(closed_extra),
        "one_extra_port_closed_sets": closed_extra,
        "natural_wider_repair": {
            "hidden_face_slots": list(wider_hidden),
            "additional_retained_face_slot": extra_slot,
            "closed": not forgotten_labels(target, wider_hidden),
            "projects_to_source_after_extra_port_removed": (
                without_extra == source.partition
            ),
        },
    }


def exchange_search(
    source: RankedFrontierState,
    target_rows: tuple[str, ...],
    depth: int,
    slab_start: int,
) -> dict:
    local_rows = range(depth + 3)
    local_columns = range(slab_start, slab_start + 6)
    cells = [(row, column) for row in local_rows for column in local_columns]
    u_cells = [cell for cell in cells if target_rows[cell[0]][cell[1]] == "U"]
    full_cells = [cell for cell in cells if target_rows[cell[0]][cell[1]] == "."]
    records = []
    for size in range(MAX_EXCHANGE + 1):
        tested = connected = forest = exact_interface = 0
        closest = None
        closest_examples = []
        removal_sets = combinations(u_cells, size) if size else [()]
        for removals in removal_sets:
            addition_sets = combinations(full_cells, size) if size else [()]
            for additions in addition_sets:
                tested += 1
                rows = [list(row) for row in target_rows]
                for row, column in removals:
                    rows[row][column] = "."
                for row, column in additions:
                    rows[row][column] = "U"
                candidate = tuple("".join(row) for row in rows)
                try:
                    trace = replay_rows(candidate)
                except ValueError:
                    continue
                connected += 1
                forest_ok, _ = forest_completion_check(candidate)
                forest += forest_ok
                signature = RootedOpenSlabSignature.extract(
                    trace[depth],
                    slab_start,
                    removed_prefix_cost(candidate, depth, slab_start),
                )
                vector = mismatch(source, signature)
                if not any(vector) and forest_ok:
                    exact_interface += 1
                if closest is None or vector < closest:
                    closest = vector
                    closest_examples = [(removals, additions)]
                elif vector == closest and len(closest_examples) < 4:
                    closest_examples.append((removals, additions))
        records.append(
            {
                "exchange_size": size,
                "tested": tested,
                "dual_connected": connected,
                "forest_completable": forest,
                "exact_straight_interfaces": exact_interface,
                "closest_mismatch": list(closest) if closest is not None else None,
                "closest_examples": [
                    {
                        "U_to_full": [list(cell) for cell in removals],
                        "full_to_U": [list(cell) for cell in additions],
                    }
                    for removals, additions in closest_examples
                ],
            }
        )
    return {
        "box": {
            "rows": [min(local_rows), max(local_rows)],
            "columns": [min(local_columns), max(local_columns)],
            "cells": len(cells),
            "U_cells": len(u_cells),
            "full_cells": len(full_cells),
        },
        "maximum_balanced_exchange_size": MAX_EXCHANGE,
        "records": records,
    }


def build_certificate() -> dict:
    patterns = pattern_inputs()
    samples = []
    for (
        source_name,
        source_orientation,
        target_name,
        target_orientation,
        depth,
        slab_start,
        symmetry_multiplicity,
    ) in SAMPLES:
        source_rows = orientation(patterns[source_name], source_orientation)
        target_rows = orientation(patterns[target_name], target_orientation)
        source = replay_rows(source_rows)[depth]
        target_trace = replay_rows(target_rows)
        target = target_trace[depth]
        straight = RootedOpenSlabSignature.extract(
            target,
            slab_start,
            removed_prefix_cost(target_rows, depth, slab_start),
        )
        samples.append(
            {
                "id": f"{source_name}-to-{target_name}",
                "source_orientation": source_orientation,
                "target_orientation": target_orientation,
                "depth": depth,
                "slab_start": slab_start,
                "closest_sample_symmetry_multiplicity": symmetry_multiplicity,
                "target_U_count": sum(row.count("U") for row in target_rows),
                "straight_mismatch": list(mismatch(source, straight)),
                "straight_forgotten_components": list(
                    straight.forgotten_only_components
                ),
                "target_forest_completable": forest_completion_check(target_rows)[0],
                "port_set_census": port_set_census(
                    source,
                    target,
                    slab_start,
                ),
                "balanced_local_exchange_census": exchange_search(
                    source, target_rows, depth, slab_start
                ),
            }
        )
    return {
        "schema": "grid-graphs.open-slab-component-repair.v1",
        "scope": {
            "samples": "all closest committed samples, reduced to three reflection classes",
            "local_exchange_box": "oriented rows 0..depth+2 and six columns starting at slab_start",
            "exchanges": "all balanced U/full exchanges of sizes zero, one, and two",
            "port_reroutes": "all 3-subsets and all 2-subsets of the complete non-root frontier",
        },
        "samples": samples,
        "conclusion": {
            "exact_equal_width_repair": False,
            "minimum_additional_retained_ports": 1,
            "additional_U_cost": 0,
            "repair_rule": "retain the forgotten component's sole face slot",
        },
    }


if __name__ == "__main__":
    print(json.dumps(build_certificate(), indent=2, sort_keys=True))
