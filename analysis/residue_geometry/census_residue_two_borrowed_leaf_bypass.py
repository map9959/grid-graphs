#!/usr/bin/env python3
"""Exhaust the borrowed-leaf full-core offset bypass grammar."""

from __future__ import annotations

import argparse
import json
from collections import Counter
from pathlib import Path

from analysis.patterns.construction_lab import forest_completion_check
from analysis.residue_geometry import (
    census_residue_two_affine_endpoint_extensions as endpoint,
)
from analysis.residue_geometry.census_residue_two_counter_interval_geometry import (
    _local_cell_violation,
    _rows,
)
from analysis.residue_geometry.census_residue_two_endpoint_slide import _translate
from analysis.residue_geometry.census_residue_two_nonleaf_spine_bypass import (
    FAR_ID,
    NEAR_ID,
    _attachment_for_edge,
    _components_by_id,
    _nodes,
    _split_geometry,
    derive_bypass_types,
)
from analysis.residue_geometry.census_residue_two_offset_spine_bypass import (
    CORE_ID,
    LOCAL_X_RANGE,
    LOCAL_Y_RANGE,
    OFFSET_SIDES,
    _local_to_vertex,
    _support,
)
from analysis.residue_geometry.check_residue_two_affine_interval_skeleton import (
    _components,
    _forced_star,
    _interval_key,
    _is_acyclic,
    _is_straight_interval,
    _standard_insertion_image,
)

Vertex = tuple[int, int]
SCHEMA = "grid-graphs.residue-two-borrowed-leaf-bypass-census.v1"
ROLES = ("beta", "gamma")


def _full_core_geometry(
    k: int,
    carrier: frozenset[Vertex],
    side: str,
    spine: frozenset[Vertex],
    offset_side: int,
) -> dict:
    split = _split_geometry(k, carrier, side, spine)
    orientation, spine_fixed, _, _ = _interval_key(spine)
    core = frozenset(
        _local_to_vertex(
            orientation,
            spine_fixed,
            split["far_moving_coordinate"],
            split["perpendicular_direction"],
            (x, offset_side),
        )
        for x in range(1, k - 4)
    )
    return {
        **split,
        "orientation": orientation,
        "spine_fixed": spine_fixed,
        "offset_side": offset_side,
        "core": core,
    }


def _context(k: int, carrier_id: str, side: str, spine_id: str, offset_side: int) -> dict:
    n = 3 * k + 2
    by_id = _components_by_id(k)
    carrier, spine = by_id[carrier_id], by_id[spine_id]
    geometry = _full_core_geometry(k, carrier, side, spine, offset_side)
    carrier_extended = carrier | geometry["ray"]
    old_attachment = _attachment_for_edge(carrier_id, spine_id, _nodes(k))
    piece_supports = {
        piece: _support(piece, n) for piece in geometry["pieces"]
    }
    near = next(piece for piece, support in piece_supports.items() if old_attachment in support)
    far = next(piece for piece in geometry["pieces"] if piece != near)
    return {
        "n": n,
        "by_id": by_id,
        "carrier": carrier,
        "spine": spine,
        "geometry": geometry,
        "carrier_extended": carrier_extended,
        "near": near,
        "far": far,
        "carrier_support": _support(carrier_extended, n),
        "core_support": _support(geometry["core"], n),
        "far_support": _support(far, n),
    }


def _role_status(component: frozenset[Vertex], role: str, context: dict) -> str:
    intended = (
        context["carrier_extended"]
        | context["geometry"]["core"]
        | context["near"]
        | context["far"]
    )
    if component & intended:
        return "role_component_overlaps_intended_geometry"
    if any(
        abs(row - other_row) + abs(column - other_column) == 1
        for row, column in component
        for other_row, other_column in intended
    ):
        return "role_component_merges_intended_geometry"
    support = _support(component, context["n"])
    carrier_hits = len(support & context["carrier_support"])
    core_hits = len(support & context["core_support"])
    far_hits = len(support & context["far_support"])
    if role == "beta":
        return (
            "valid" if (carrier_hits, core_hits, far_hits) == (1, 1, 0)
            else "beta_singleton_owner_equations_fail"
        )
    return (
        "valid" if (carrier_hits, core_hits, far_hits) == (0, 1, 1)
        else "gamma_singleton_owner_equations_fail"
    )


def _component_signature(component: frozenset[Vertex], context: dict) -> tuple[Vertex, ...]:
    geometry = context["geometry"]
    orientation = geometry["orientation"]
    fixed = geometry["spine_fixed"]
    far = geometry["far_moving_coordinate"]
    direction = geometry["perpendicular_direction"]
    result = []
    for row, column in component:
        result.append(
            (
                ((row - fixed) * direction, column - far)
                if orientation == "H"
                else ((column - fixed) * direction, row - far)
            )
        )
    return tuple(sorted(result))


def _target_role_placements(
    source_component: frozenset[Vertex], role: str, context: dict
) -> dict[tuple[Vertex, ...], Vertex]:
    """Enumerate translations only when every target center lies in the local box."""
    source_anchor = min(source_component)
    placements = {}
    geometry = context["geometry"]
    for x in LOCAL_X_RANGE:
        for y in LOCAL_Y_RANGE:
            target_anchor = _local_to_vertex(
                geometry["orientation"], geometry["spine_fixed"],
                geometry["far_moving_coordinate"], geometry["perpendicular_direction"],
                (x, y),
            )
            delta = target_anchor[0] - source_anchor[0], target_anchor[1] - source_anchor[1]
            moved = _translate(source_component, delta)
            if not all(0 <= row < context["n"] and 0 <= column < context["n"] for row, column in moved):
                continue
            signature = _component_signature(moved, context)
            if not all(
                min(LOCAL_X_RANGE) <= local_x <= max(LOCAL_X_RANGE)
                and min(LOCAL_Y_RANGE) <= local_y <= max(LOCAL_Y_RANGE)
                for local_x, local_y in signature
            ):
                continue
            if _role_status(moved, role, context) == "valid":
                placements[signature] = delta
    return placements


def _failed_window_vertices(bypass_type: dict, offset_side: int) -> set[Vertex]:
    """Recover the k=7 individual singleton windows from the failed topology."""
    k = 7
    carrier_id, spine_id = bypass_type["transported_carriers"][0], bypass_type["transported_spines"][0]
    context = _context(k, carrier_id, bypass_type["side"], spine_id, offset_side)
    geometry = context["geometry"]
    # At k=7 the failed shortened core was empty.  These are exactly the local
    # singleton centers satisfying one endpoint role before pair compatibility.
    windows = set()
    occupied = context["carrier_extended"] | context["near"] | context["far"]
    for x in LOCAL_X_RANGE:
        for y in LOCAL_Y_RANGE:
            vertex = _local_to_vertex(
                geometry["orientation"], geometry["spine_fixed"],
                geometry["far_moving_coordinate"], geometry["perpendicular_direction"],
                (x, y),
            )
            if not (0 <= vertex[0] < context["n"] and 0 <= vertex[1] < context["n"]):
                continue
            component = frozenset((vertex,))
            if component & occupied or any(
                abs(vertex[0] - row) + abs(vertex[1] - column) == 1
                for row, column in occupied
            ):
                continue
            support = _support(component, context["n"])
            carrier_hits = len(support & context["carrier_support"])
            far_hits = len(support & context["far_support"])
            if (carrier_hits == 1 and far_hits == 0) or (carrier_hits == 0 and far_hits == 1):
                windows.add(vertex)
    return windows


def _constant_leaf_chains(bypass_type: dict, offset_side: int) -> list[dict]:
    windows = _failed_window_vertices(bypass_type, offset_side)
    components = {k: _components_by_id(k) for k in (7, 8, 9)}
    nodes = {k: _nodes(k) for k in (7, 8, 9)}
    map78, map89 = endpoint._owner_map(7), endpoint._owner_map(8)
    excluded = {bypass_type["carrier"], bypass_type["blocker"], bypass_type["spine"]}
    result = []
    for source, component in components[7].items():
        if source in excluded:
            continue
        middle, target = map78[source], map89[map78[source]]
        names = (source, middle, target)
        if not all(not nodes[k][name]["children"] for k, name in zip((7, 8, 9), names)):
            continue
        lengths = [len(components[k][name]) for k, name in zip((7, 8, 9), names)]
        if len(set(lengths)) != 1:
            continue
        if not any(
            _support(component, 23) & _support(frozenset((window,)), 23)
            for window in windows
        ):
            continue
        result.append({
            "source": source,
            "transported": list(names),
            "length": lengths[0],
        })
    return result


def derive_borrowed_choices() -> dict:
    types = derive_bypass_types()
    choices = []
    attempts = []
    for type_index, bypass_type in enumerate(types):
        for offset_side in OFFSET_SIDES:
            leaf_chains = _constant_leaf_chains(bypass_type, offset_side)
            for blocker_role in ROLES:
                second_role = "gamma" if blocker_role == "beta" else "beta"
                blocker_statuses = []
                contexts = []
                for k, carrier, blocker, spine in zip(
                    (7, 8, 9),
                    bypass_type["transported_carriers"],
                    bypass_type["transported_blockers"],
                    bypass_type["transported_spines"],
                ):
                    context = _context(k, carrier, bypass_type["side"], spine, offset_side)
                    contexts.append(context)
                    moved_blocker = _translate(
                        context["by_id"][blocker], tuple(bypass_type["blocker_translation"])
                    )
                    blocker_statuses.append(_role_status(moved_blocker, blocker_role, context))
                attempt = {
                    "type_index": type_index,
                    "offset_side": offset_side,
                    "blocker_role": blocker_role,
                    "second_role": second_role,
                    "blocker_statuses": blocker_statuses,
                    "adjacent_constant_leaf_count": len(leaf_chains),
                    "adjacent_constant_leaves": leaf_chains,
                    "leaf_attempts": [],
                }
                if blocker_statuses != ["valid", "valid", "valid"]:
                    attempts.append(attempt)
                    continue
                for leaf_chain in leaf_chains:
                    signatures_by_k = []
                    placements_by_k = []
                    for k, leaf_name, context in zip((7, 8, 9), leaf_chain["transported"], contexts):
                        placements = _target_role_placements(
                            context["by_id"][leaf_name], second_role, context
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
                            "offset_side": offset_side,
                            "blocker_role": blocker_role,
                            "second_role": second_role,
                            "second_leaf": leaf_chain,
                            "target_signature": [list(item) for item in signature],
                            "second_leaf_translations": [
                                list(placements[signature]) for placements in placements_by_k
                            ],
                        })
                attempts.append(attempt)
    return {"types": types, "attempts": attempts, "choices": choices}


def _evaluate_choice(k: int, choice: dict) -> dict:
    bypass_type = derive_bypass_types()[choice["type_index"]]
    index = k - 7
    carrier_id = bypass_type["transported_carriers"][index]
    blocker_id = bypass_type["transported_blockers"][index]
    spine_id = bypass_type["transported_spines"][index]
    second_id = choice["second_leaf"]["transported"][index]
    context = _context(k, carrier_id, bypass_type["side"], spine_id, choice["offset_side"])
    by_id = context["by_id"]
    blocker, second = by_id[blocker_id], by_id[second_id]
    moved_blocker = _translate(blocker, tuple(bypass_type["blocker_translation"]))
    moved_second = _translate(second, tuple(choice["second_leaf_translations"][index]))
    geometry = context["geometry"]
    record = {
        "k": k,
        "carrier": carrier_id,
        "blocker": blocker_id,
        "spine": spine_id,
        "second_leaf": second_id,
        "offset_side": choice["offset_side"],
        "blocker_role": choice["blocker_role"],
        "second_role": choice["second_role"],
        "carrier_ray": [list(vertex) for vertex in sorted(geometry["ray"])],
        "removed_spine_segment": [list(vertex) for vertex in sorted(geometry["removed"])],
        "full_offset_core": [list(vertex) for vertex in sorted(geometry["core"])],
        "moved_blocker": [list(vertex) for vertex in sorted(moved_blocker)],
        "moved_second_leaf": [list(vertex) for vertex in sorted(moved_second)],
    }
    base = endpoint._preserved(k)
    additions = set(geometry["ray"]) | set(geometry["core"]) | set(moved_blocker) | set(moved_second)
    vertices = (base - blocker - second - geometry["removed"]) | additions
    target = 3 * k * k + 7 * k
    if len(vertices) != target:
        return {**record, "status": "wrong_target_count_due_to_overlap", "expected": target, "observed": len(vertices)}
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
    required = [geometry["core"], moved_blocker, moved_second, *geometry["pieces"]]
    if not all(component in components for component in required):
        return {**record, "status": "declared_component_not_exact"}

    # The owner equations and exact components identify beta/gamma.  Continue
    # with the complete star graph and require a tree with only the two old leaf
    # parent edges and split-spine replacement changed.
    labels = {
        geometry["core"]: CORE_ID,
        moved_blocker: blocker_id,
        moved_second: second_id,
        context["near"]: NEAR_ID,
        context["far"]: FAR_ID,
    }
    used = {blocker_id, second_id, spine_id}
    for component in components:
        if component in labels:
            continue
        overlaps = [
            name for name, old in by_id.items()
            if name not in used and component & old
        ]
        if len(overlaps) != 1:
            return {**record, "status": "noninjective_component_transport"}
        labels[component] = overlaps[0]
        used.add(overlaps[0])
    if len(used) != len(by_id):
        return {**record, "status": "missing_old_component"}
    stars = {component: _forced_star(component, context["n"]) for component in components}
    if not all(_is_acyclic(edges) for edges, _ in stars.values()):
        return {**record, "status": "cyclic_interval_star"}
    observed_edges = []
    for left_index, left in enumerate(components):
        for right in components[left_index + 1:]:
            intersection = stars[left][1] & stars[right][1]
            if len(intersection) > 1:
                return {**record, "status": "multiple_star_intersection", "detail": {"left": labels[left], "right": labels[right], "size": len(intersection)}}
            if intersection:
                observed_edges.append(frozenset((labels[left], labels[right])))
    if len(observed_edges) != len(components) - 1:
        return {**record, "status": "incidence_not_tree_by_edge_count"}
    forest_ok, reason = forest_completion_check(_rows(vertices, context["n"]))
    if not forest_ok:
        return {**record, "status": "forced_graph_not_forest", "detail": reason}
    return {**record, "status": "realization", "preserved_count": len(vertices)}


def replay_choice(k: int, choice: dict) -> dict:
    return _evaluate_choice(k, choice)


def build_report() -> dict:
    derivation = derive_borrowed_choices()
    core_adjacencies = []
    for type_index, bypass_type in enumerate(derivation["types"]):
        for offset_side in OFFSET_SIDES:
            for k, carrier, spine in zip(
                (7, 8, 9),
                bypass_type["transported_carriers"],
                bypass_type["transported_spines"],
            ):
                context = _context(k, carrier, bypass_type["side"], spine, offset_side)
                pairs = [
                    [list(core_vertex), list(carrier_vertex)]
                    for core_vertex in sorted(context["geometry"]["core"])
                    for carrier_vertex in sorted(context["carrier_extended"])
                    if abs(core_vertex[0] - carrier_vertex[0])
                    + abs(core_vertex[1] - carrier_vertex[1]) == 1
                ]
                core_adjacencies.append({
                    "type_index": type_index,
                    "offset_side": offset_side,
                    "k": k,
                    "adjacent_center_pairs": pairs,
                    "status": "core_merges_carrier" if pairs else "separate",
                })
    chains = []
    terminal = Counter()
    width_terminal = {k: Counter() for k in (7, 8, 9)}
    for choice in derivation["choices"]:
        evaluations = [_evaluate_choice(k, choice) for k in (7, 8, 9)]
        for evaluation in evaluations:
            width_terminal[evaluation["k"]][evaluation["status"]] += 1
        first_failure = next(
            (item["status"] for item in evaluations if item["status"] != "realization"),
            "realization",
        )
        terminal[first_failure] += 1
        coordinate_nesting = []
        for source, target in zip(evaluations, evaluations[1:]):
            source_added = {
                _standard_insertion_image(tuple(vertex))
                for field in ("carrier_ray", "full_offset_core", "moved_blocker", "moved_second_leaf")
                for vertex in source[field]
            }
            target_added = {
                tuple(vertex)
                for field in ("carrier_ray", "full_offset_core", "moved_blocker", "moved_second_leaf")
                for vertex in target[field]
            }
            coordinate_nesting.append(source_added <= target_added)
        stable = all(item["status"] == "realization" for item in evaluations)
        stable &= all(coordinate_nesting)
        chains.append({
            "choice": choice,
            "width_evaluations": evaluations,
            "coordinate_images_nest": coordinate_nesting,
            "status": "stable_realization" if stable else "obstructed",
        })
    survivors = [chain for chain in chains if chain["status"] == "stable_realization"]
    blocker_histogram = Counter(
        status
        for attempt in derivation["attempts"]
        for status in attempt["blocker_statuses"]
    )
    return {
        "schema": SCHEMA,
        "checker": "residue_two_borrowed_leaf_bypass_census",
        "status": "stable_realization" if survivors else "complete_borrowed_leaf_bypass_obstruction",
        "grammar": {
            "source_types": len(derivation["types"]),
            "offset_sides": list(OFFSET_SIDES),
            "blocker_role_assignments": list(ROLES),
            "role_attempts": len(derivation["attempts"]),
            "borrowed_choices": len(derivation["choices"]),
            "other_edits": "none",
        },
        "derivation": derivation,
        "blocker_role_status_histogram": dict(sorted(blocker_histogram.items())),
        "intrinsic_core_carrier_adjacency": core_adjacencies,
        "terminal_histogram": dict(sorted(terminal.items())),
        "width_terminal_histograms": {
            str(k): dict(sorted(values.items())) for k, values in width_terminal.items()
        },
        "chains": chains,
        "survivors": survivors,
        "next_topology": {
            "name": "two-layer dogleg bypass",
            "specification": (
                "move the full core from local y=+-1 to y=+-2 and use the prescribed blocker "
                "plus one adjacent constant leaf as the two short dogleg rungs"
            ),
            "count": "full core relocation and two leaf translations are zero-net; carrier is +1 per step",
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
