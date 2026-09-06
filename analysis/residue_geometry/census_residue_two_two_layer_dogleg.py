#!/usr/bin/env python3
"""Exhaust the final two-layer dogleg bypass grammar."""

from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path

from analysis.residue_geometry import census_residue_two_affine_endpoint_extensions as endpoint
from analysis.residue_geometry.census_residue_two_counter_interval_geometry import _local_cell_violation, _rows
from analysis.residue_geometry.census_residue_two_endpoint_slide import _translate
from analysis.residue_geometry.census_residue_two_nonleaf_spine_bypass import (
    FAR_ID,
    NEAR_ID,
    _attachment_for_edge,
    _components_by_id,
    _nodes,
    derive_bypass_types,
)
from analysis.residue_geometry.census_residue_two_offset_spine_bypass import CORE_ID
from analysis.residue_geometry.census_residue_two_borrowed_leaf_bypass import (
    _component_signature,
    _constant_leaf_chains,
    _context,
    _role_status,
    _target_role_placements,
)
from analysis.residue_geometry.check_residue_two_affine_interval_skeleton import (
    _components,
    _forced_star,
    _is_acyclic,
    _is_straight_interval,
    _standard_insertion_image,
)
from analysis.patterns.construction_lab import forest_completion_check


Vertex = tuple[int, int]
SCHEMA = "grid-graphs.residue-two-two-layer-dogleg-census.v1"
DOGLEG_SIDES = (-2, 2)
ROLES = ("beta", "gamma")


def _rung_side(dogleg_side: int) -> int:
    return -1 if dogleg_side < 0 else 1


def _on_rung_line(component: frozenset[Vertex], context: dict, dogleg_side: int) -> bool:
    signature = _component_signature(component, context)
    return bool(signature) and all(y == _rung_side(dogleg_side) for _, y in signature)


def _rung_placements(
    source: frozenset[Vertex], role: str, context: dict, dogleg_side: int
) -> dict[tuple[Vertex, ...], Vertex]:
    return {
        signature: delta
        for signature, delta in _target_role_placements(source, role, context).items()
        if all(y == _rung_side(dogleg_side) for _, y in signature)
    }


def derive_dogleg_choices() -> dict:
    types = derive_bypass_types()
    attempts = []
    choices = []
    for type_index, bypass_type in enumerate(types):
        for dogleg_side in DOGLEG_SIDES:
            # Adjacency remains tied to the failed immediate-offset connector
            # window on the same side; no new source leaves are introduced.
            leaf_chains = _constant_leaf_chains(
                bypass_type, _rung_side(dogleg_side)
            )
            for blocker_role in ROLES:
                second_role = "gamma" if blocker_role == "beta" else "beta"
                contexts = []
                blocker_statuses = []
                blocker_signatures = []
                for k, carrier, blocker, spine in zip(
                    (7, 8, 9),
                    bypass_type["transported_carriers"],
                    bypass_type["transported_blockers"],
                    bypass_type["transported_spines"],
                ):
                    context = _context(
                        k, carrier, bypass_type["side"], spine, dogleg_side
                    )
                    contexts.append(context)
                    moved_blocker = _translate(
                        context["by_id"][blocker],
                        tuple(bypass_type["blocker_translation"]),
                    )
                    status = _role_status(moved_blocker, blocker_role, context)
                    if status == "valid" and not _on_rung_line(
                        moved_blocker, context, dogleg_side
                    ):
                        status = "prescribed_blocker_not_on_rung_line"
                    blocker_statuses.append(status)
                    blocker_signatures.append(
                        [list(item) for item in _component_signature(moved_blocker, context)]
                    )
                attempt = {
                    "type_index": type_index,
                    "dogleg_side": dogleg_side,
                    "rung_side": _rung_side(dogleg_side),
                    "blocker_role": blocker_role,
                    "second_role": second_role,
                    "blocker_statuses": blocker_statuses,
                    "blocker_signatures": blocker_signatures,
                    "adjacent_constant_leaves": leaf_chains,
                    "leaf_attempts": [],
                }
                if blocker_statuses != ["valid", "valid", "valid"]:
                    attempts.append(attempt)
                    continue
                for leaf_chain in leaf_chains:
                    placements_by_k = []
                    signatures_by_k = []
                    for k, leaf_name, context in zip(
                        (7, 8, 9), leaf_chain["transported"], contexts
                    ):
                        placements = _rung_placements(
                            context["by_id"][leaf_name],
                            second_role,
                            context,
                            dogleg_side,
                        )
                        placements_by_k.append(placements)
                        signatures_by_k.append(set(placements))
                    common = set.intersection(*signatures_by_k)
                    leaf_record = {
                        "leaf": leaf_chain,
                        "signature_counts": [len(items) for items in signatures_by_k],
                        "common_signature_count": len(common),
                    }
                    attempt["leaf_attempts"].append(leaf_record)
                    for signature in sorted(common):
                        choices.append({
                            "type_index": type_index,
                            "dogleg_side": dogleg_side,
                            "rung_side": _rung_side(dogleg_side),
                            "blocker_role": blocker_role,
                            "second_role": second_role,
                            "second_leaf": leaf_chain,
                            "target_signature": [list(item) for item in signature],
                            "second_leaf_translations": [
                                list(placements[signature])
                                for placements in placements_by_k
                            ],
                        })
                attempts.append(attempt)
    return {"types": types, "attempts": attempts, "choices": choices}


def _connected(labels: set[str], edges: list[frozenset[str]]) -> bool:
    if not labels:
        return True
    adjacency = {label: set() for label in labels}
    for edge in edges:
        left, right = tuple(edge)
        adjacency[left].add(right)
        adjacency[right].add(left)
    reached = {next(iter(labels))}
    changed = True
    while changed:
        expanded = reached | set().union(*(adjacency[node] for node in reached))
        changed = expanded != reached
        reached = expanded
    return reached == labels


def _evaluate_choice(k: int, choice: dict) -> dict:
    types = derive_bypass_types()
    bypass_type = types[choice["type_index"]]
    index = k - 7
    carrier_id = bypass_type["transported_carriers"][index]
    blocker_id = bypass_type["transported_blockers"][index]
    spine_id = bypass_type["transported_spines"][index]
    second_id = choice["second_leaf"]["transported"][index]
    context = _context(
        k, carrier_id, bypass_type["side"], spine_id, choice["dogleg_side"]
    )
    blocker, second = context["by_id"][blocker_id], context["by_id"][second_id]
    moved_blocker = _translate(
        blocker, tuple(bypass_type["blocker_translation"])
    )
    moved_second = _translate(
        second, tuple(choice["second_leaf_translations"][index])
    )
    geometry = context["geometry"]
    record = {
        "k": k,
        "carrier": carrier_id,
        "blocker": blocker_id,
        "spine": spine_id,
        "second_leaf": second_id,
        "dogleg_side": choice["dogleg_side"],
        "rung_side": choice["rung_side"],
        "blocker_role": choice["blocker_role"],
        "second_role": choice["second_role"],
        "carrier_ray": [list(vertex) for vertex in sorted(geometry["ray"])],
        "removed_spine_segment": [
            list(vertex) for vertex in sorted(geometry["removed"])
        ],
        "full_dogleg_core": [list(vertex) for vertex in sorted(geometry["core"])],
        "moved_blocker": [list(vertex) for vertex in sorted(moved_blocker)],
        "moved_second_leaf": [list(vertex) for vertex in sorted(moved_second)],
    }
    base = endpoint._preserved(k)
    additions = (
        set(geometry["ray"])
        | set(geometry["core"])
        | set(moved_blocker)
        | set(moved_second)
    )
    vertices = (
        base - blocker - second - geometry["removed"]
    ) | additions
    target = 3 * k * k + 7 * k
    if len(vertices) != target:
        return {
            **record,
            "status": "wrong_target_count_due_to_overlap",
            "expected": target,
            "observed": len(vertices),
        }
    violation = _local_cell_violation(
        vertices,
        set(blocker) | set(second) | set(geometry["removed"]) | additions,
        context["n"],
    )
    if violation is not None:
        return {**record, "status": "forbidden_unit_cell", "detail": violation}
    components = _components(vertices, context["n"])
    if not all(_is_straight_interval(component) for component in components):
        return {**record, "status": "nonstraight_component"}
    required = [
        geometry["core"], moved_blocker, moved_second, *geometry["pieces"]
    ]
    if not all(component in components for component in required):
        return {**record, "status": "declared_component_not_exact"}

    nodes = _nodes(k)
    old_attachment = _attachment_for_edge(carrier_id, spine_id, nodes)
    near = context["near"]
    far = context["far"]
    labels = {
        geometry["core"]: CORE_ID,
        moved_blocker: blocker_id,
        moved_second: second_id,
        near: NEAR_ID,
        far: FAR_ID,
    }
    used = {blocker_id, second_id, spine_id}
    for component in components:
        if component in labels:
            continue
        overlaps = [
            name for name, old in context["by_id"].items()
            if name not in used and component & old
        ]
        if len(overlaps) != 1:
            return {**record, "status": "noninjective_component_transport"}
        labels[component] = overlaps[0]
        used.add(overlaps[0])
    if len(used) != len(context["by_id"]):
        return {**record, "status": "missing_old_component"}
    stars = {
        component: _forced_star(component, context["n"])
        for component in components
    }
    if not all(_is_acyclic(edges) for edges, _ in stars.values()):
        return {**record, "status": "cyclic_interval_star"}
    observed_edges = []
    for left_index, left in enumerate(components):
        for right in components[left_index + 1:]:
            intersection = stars[left][1] & stars[right][1]
            if len(intersection) > 1:
                return {
                    **record,
                    "status": "multiple_star_intersection",
                    "detail": {
                        "left": labels[left],
                        "right": labels[right],
                        "size": len(intersection),
                    },
                }
            if intersection:
                observed_edges.append(frozenset((labels[left], labels[right])))
    label_set = set(labels.values())
    if len(observed_edges) != len(components) - 1 or not _connected(
        label_set, observed_edges
    ):
        return {**record, "status": "incidence_not_tree"}
    forest_ok, reason = forest_completion_check(_rows(vertices, context["n"]))
    if not forest_ok:
        return {
            **record,
            "status": "forced_graph_not_forest",
            "detail": reason,
        }
    return {
        **record,
        "status": "realization",
        "retained_near_owner": list(old_attachment),
        "preserved_count": len(vertices),
    }


def replay_choice(k: int, choice: dict) -> dict:
    return _evaluate_choice(k, choice)


def build_report() -> dict:
    derivation = derive_dogleg_choices()
    chains = []
    terminal = Counter()
    width_terminal = {k: Counter() for k in (7, 8, 9)}
    for choice in derivation["choices"]:
        evaluations = [_evaluate_choice(k, choice) for k in (7, 8, 9)]
        for evaluation in evaluations:
            width_terminal[evaluation["k"]][evaluation["status"]] += 1
        first_failure = next(
            (
                item["status"]
                for item in evaluations
                if item["status"] != "realization"
            ),
            "realization",
        )
        terminal[first_failure] += 1
        coordinate_nesting = []
        for source, target in zip(evaluations, evaluations[1:]):
            source_added = {
                _standard_insertion_image(tuple(vertex))
                for field in (
                    "carrier_ray",
                    "full_dogleg_core",
                    "moved_blocker",
                    "moved_second_leaf",
                )
                for vertex in source[field]
            }
            target_added = {
                tuple(vertex)
                for field in (
                    "carrier_ray",
                    "full_dogleg_core",
                    "moved_blocker",
                    "moved_second_leaf",
                )
                for vertex in target[field]
            }
            coordinate_nesting.append(source_added <= target_added)
        stable = all(
            item["status"] == "realization" for item in evaluations
        ) and all(coordinate_nesting)
        chains.append({
            "choice": choice,
            "width_evaluations": evaluations,
            "coordinate_images_nest": coordinate_nesting,
            "status": "stable_realization" if stable else "obstructed",
        })
    survivors = [
        chain for chain in chains if chain["status"] == "stable_realization"
    ]
    blocker_histogram = Counter(
        status
        for attempt in derivation["attempts"]
        for status in attempt["blocker_statuses"]
    )
    attempt_terminal = Counter(
        next(
            (status for status in attempt["blocker_statuses"] if status != "valid"),
            "valid",
        )
        for attempt in derivation["attempts"]
    )
    return {
        "schema": SCHEMA,
        "checker": "residue_two_two_layer_dogleg_census",
        "status": (
            "stable_realization"
            if survivors
            else "complete_two_layer_dogleg_obstruction"
        ),
        "grammar": {
            "source_types": len(derivation["types"]),
            "dogleg_sides": list(DOGLEG_SIDES),
            "rung_sides": [-1, 1],
            "blocker_roles": list(ROLES),
            "role_attempts": len(derivation["attempts"]),
            "materialized_choices": len(derivation["choices"]),
            "other_edits": "none",
        },
        "derivation": derivation,
        "blocker_role_status_histogram": dict(sorted(blocker_histogram.items())),
        "attempt_terminal_histogram": dict(sorted(attempt_terminal.items())),
        "terminal_histogram": dict(sorted(terminal.items())),
        "width_terminal_histograms": {
            str(k): dict(sorted(values.items()))
            for k, values in width_terminal.items()
        },
        "chains": chains,
        "survivors": survivors,
        "line_status": {
            "affine_surgery_line_exhausted": not survivors,
            "reason": (
                "the final witness-derived offset and borrowed-leaf dogleg has no transported "
                "connector grammar; all prior narrower affine surgeries are recorded complete"
            ),
            "next_topology": None,
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    payload = json.dumps(build_report(), indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(payload)
    else:
        print(payload, end="")


if __name__ == "__main__":
    main()
