#!/usr/bin/env python3
"""Exhaust the exact offset-spine bypass with two connector leaves."""

from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path

import census_residue_two_affine_endpoint_extensions as endpoint
from census_residue_two_counter_interval_geometry import _local_cell_violation, _rows
from census_residue_two_endpoint_slide import _translate
from census_residue_two_nonleaf_spine_bypass import (
    FAR_ID,
    NEAR_ID,
    _attachment_for_edge,
    _components_by_id,
    _nodes,
    _split_geometry,
    derive_bypass_types,
)
from check_residue_two_affine_interval_skeleton import (
    _components,
    _forced_star,
    _interval_key,
    _is_acyclic,
    _is_straight_interval,
    _standard_insertion_image,
)
from construction_lab import forest_completion_check


Vertex = tuple[int, int]
SCHEMA = "grid-graphs.residue-two-offset-spine-bypass-census.v1"
CORE_ID = "O:core"
BETA_ID = "O:beta"
GAMMA_ID = "O:gamma"
OFFSET_SIDES = (-1, 1)
LOCAL_X_RANGE = range(-2, 5)
LOCAL_Y_RANGE = range(-3, 4)


def _local_to_vertex(
    spine_orientation: str,
    spine_fixed: int,
    far: int,
    direction: int,
    signature: Vertex,
) -> Vertex:
    x, y = signature
    return (
        (spine_fixed + direction * x, far + y)
        if spine_orientation == "H"
        else (far + y, spine_fixed + direction * x)
    )


def _vertex_to_local(
    spine_orientation: str,
    spine_fixed: int,
    far: int,
    direction: int,
    vertex: Vertex,
) -> Vertex:
    row, column = vertex
    return (
        ((row - spine_fixed) * direction, column - far)
        if spine_orientation == "H"
        else ((column - spine_fixed) * direction, row - far)
    )


def _offset_geometry(
    k: int,
    carrier: frozenset[Vertex],
    side: str,
    spine: frozenset[Vertex],
    offset_side: int,
) -> dict:
    split = _split_geometry(k, carrier, side, spine)
    orientation, spine_fixed, _, _ = _interval_key(spine)
    core_length = k - 7
    far = split["far_moving_coordinate"]
    direction = split["perpendicular_direction"]
    core = frozenset(
        _local_to_vertex(
            orientation, spine_fixed, far, direction, (x, offset_side)
        )
        for x in range(1, core_length + 1)
    )
    return {
        **split,
        "orientation": orientation,
        "spine_fixed": spine_fixed,
        "core_length": core_length,
        "core": core,
        "offset_side": offset_side,
    }


def _support(component: frozenset[Vertex], n: int) -> frozenset[Vertex]:
    return _forced_star(component, n)[1]


def _connector_signatures(
    k: int,
    carrier_id: str,
    side: str,
    spine_id: str,
    offset_side: int,
) -> tuple[set[tuple[Vertex, Vertex]], dict]:
    """Solve only the required local singleton-owner equations."""
    n = 3 * k + 2
    by_id = _components_by_id(k)
    carrier, spine = by_id[carrier_id], by_id[spine_id]
    geometry = _offset_geometry(k, carrier, side, spine, offset_side)
    ray, core = geometry["ray"], geometry["core"]
    carrier_extended = carrier | ray
    old_attachment = _attachment_for_edge(carrier_id, spine_id, _nodes(k))
    piece_supports = {
        piece: _support(piece, n) for piece in geometry["pieces"]
    }
    near = next(piece for piece, support in piece_supports.items() if old_attachment in support)
    far_piece = next(piece for piece in geometry["pieces"] if piece != near)
    carrier_support, far_support = _support(carrier_extended, n), _support(far_piece, n)
    core_support = _support(core, n) if core else frozenset()

    local_vertices = {
        signature: _local_to_vertex(
            geometry["orientation"],
            geometry["spine_fixed"],
            geometry["far_moving_coordinate"],
            geometry["perpendicular_direction"],
            signature,
        )
        for signature in ((x, y) for x in LOCAL_X_RANGE for y in LOCAL_Y_RANGE)
    }
    local_vertices = {
        signature: vertex for signature, vertex in local_vertices.items()
        if 0 <= vertex[0] < n and 0 <= vertex[1] < n
    }
    occupied = carrier_extended | near | far_piece | core
    singleton_supports = {
        signature: _support(frozenset((vertex,)), n)
        for signature, vertex in local_vertices.items()
        if vertex not in occupied
        and all(abs(vertex[0] - row) + abs(vertex[1] - column) != 1
                for row, column in occupied)
    }
    beta_candidates = []
    for beta_signature, beta_support in singleton_supports.items():
        if len(beta_support & carrier_support) != 1 or beta_support & far_support:
            continue
        if core and len(beta_support & core_support) != 1:
            continue
        beta_candidates.append(beta_signature)
    gamma_candidates = []
    for gamma_signature, gamma_support in singleton_supports.items():
        if len(gamma_support & far_support) != 1 or gamma_support & carrier_support:
            continue
        if core and len(gamma_support & core_support) != 1:
            continue
        gamma_candidates.append(gamma_signature)

    result = set()
    terminal = Counter()
    samples = {}
    pair_attempts = 0
    for beta_signature in beta_candidates:
        beta_support = singleton_supports[beta_signature]
        beta_vertex = local_vertices[beta_signature]
        for gamma_signature in gamma_candidates:
            gamma_support = singleton_supports[gamma_signature]
            pair_attempts += 1
            if gamma_signature == beta_signature:
                terminal["same_connector_center"] += 1
                samples.setdefault("same_connector_center", [list(beta_signature), list(gamma_signature)])
                continue
            gamma_vertex = local_vertices[gamma_signature]
            if abs(beta_vertex[0] - gamma_vertex[0]) + abs(beta_vertex[1] - gamma_vertex[1]) == 1:
                terminal["connector_centers_merge"] += 1
                samples.setdefault("connector_centers_merge", [list(beta_signature), list(gamma_signature)])
                continue
            intersection = beta_support & gamma_support
            if core:
                if intersection:
                    terminal["undeclared_beta_gamma_intersection"] += 1
                    samples.setdefault(
                        "undeclared_beta_gamma_intersection",
                        [list(beta_signature), list(gamma_signature)],
                    )
                    continue
            elif len(intersection) != 1:
                terminal["empty_core_requires_singleton_beta_gamma_owner"] += 1
                samples.setdefault(
                    "empty_core_requires_singleton_beta_gamma_owner",
                    [list(beta_signature), list(gamma_signature)],
                )
                continue
            result.add((beta_signature, gamma_signature))
            terminal["valid"] += 1
    return result, {
        "local_center_count": len(local_vertices),
        "separate_singleton_center_count": len(singleton_supports),
        "beta_candidate_count": len(beta_candidates),
        "gamma_candidate_count": len(gamma_candidates),
        "ordered_pair_attempts": pair_attempts,
        "terminal_histogram": dict(sorted(terminal.items())),
        "first_replay_by_terminal_status": dict(sorted(samples.items())),
        "valid_signatures": [
            {"beta": list(beta), "gamma": list(gamma)}
            for beta, gamma in sorted(result)
        ],
    }


def derive_offset_choices() -> dict:
    """Intersect local connector signatures across all three widths."""
    types = derive_bypass_types()
    choices = []
    rejected = []
    for type_index, bypass_type in enumerate(types):
        for offset_side in OFFSET_SIDES:
            signatures_by_k = []
            owner_censuses = []
            for k, carrier, spine in zip(
                (7, 8, 9),
                bypass_type["transported_carriers"],
                bypass_type["transported_spines"],
            ):
                signatures, owner_census = _connector_signatures(
                    k, carrier, bypass_type["side"], spine, offset_side
                )
                signatures_by_k.append(signatures)
                owner_censuses.append({"k": k, **owner_census})
            common = set.intersection(*signatures_by_k)
            record = {
                "type_index": type_index,
                "offset_side": offset_side,
                "signature_counts": [len(items) for items in signatures_by_k],
                "common_signature_count": len(common),
                "owner_equation_censuses": owner_censuses,
            }
            if not common:
                rejected.append(record)
                continue
            for beta, gamma in sorted(common):
                choices.append({
                    **record,
                    "beta_signature": list(beta),
                    "gamma_signature": list(gamma),
                })
    return {
        "types": types,
        "offset_attempts": len(types) * len(OFFSET_SIDES),
        "choices": choices,
        "rejected_offsets": rejected,
    }


def replay_owner_census(k: int, type_index: int, offset_side: int) -> dict:
    """Replay one hard-capped local connector-owner census."""
    bypass_type = derive_bypass_types()[type_index]
    _, census = _connector_signatures(
        k,
        bypass_type["transported_carriers"][k - 7],
        bypass_type["side"],
        bypass_type["transported_spines"][k - 7],
        offset_side,
    )
    return {"k": k, **census}


def _evaluate_offset(
    k: int,
    bypass_type: dict,
    carrier_id: str,
    blocker_id: str,
    spine_id: str,
    offset_side: int,
    beta_signature: Vertex,
    gamma_signature: Vertex,
) -> dict:
    n = 3 * k + 2
    base = endpoint._preserved(k)
    by_id = _components_by_id(k)
    carrier, blocker, spine = by_id[carrier_id], by_id[blocker_id], by_id[spine_id]
    geometry = _offset_geometry(k, carrier, bypass_type["side"], spine, offset_side)
    beta = _local_to_vertex(
        geometry["orientation"], geometry["spine_fixed"],
        geometry["far_moving_coordinate"], geometry["perpendicular_direction"],
        beta_signature,
    )
    gamma = _local_to_vertex(
        geometry["orientation"], geometry["spine_fixed"],
        geometry["far_moving_coordinate"], geometry["perpendicular_direction"],
        gamma_signature,
    )
    moved_blocker = _translate(blocker, tuple(bypass_type["blocker_translation"]))
    ray, removed, core = geometry["ray"], geometry["removed"], geometry["core"]
    record = {
        "k": k,
        "carrier": carrier_id,
        "side": bypass_type["side"],
        "blocker": blocker_id,
        "spine": spine_id,
        "blocker_translation": bypass_type["blocker_translation"],
        "offset_side": offset_side,
        "beta_signature": list(beta_signature),
        "gamma_signature": list(gamma_signature),
        "carrier_ray": [list(vertex) for vertex in sorted(ray)],
        "removed_spine_segment": [list(vertex) for vertex in sorted(removed)],
        "offset_core": [list(vertex) for vertex in sorted(core)],
        "beta_connector": list(beta),
        "gamma_connector": list(gamma),
        "moved_blocker": [list(vertex) for vertex in sorted(moved_blocker)],
    }
    additions = set(ray) | set(core) | {beta, gamma} | set(moved_blocker)
    vertices = (base - blocker - removed) | additions
    target = 3 * k * k + 7 * k
    if len(vertices) != target:
        return {
            **record,
            "status": "wrong_target_count_due_to_overlap",
            "expected": target,
            "observed": len(vertices),
        }
    changed = set(blocker) | set(moved_blocker) | set(removed) | additions
    violation = _local_cell_violation(vertices, changed, n)
    if violation is not None:
        return {**record, "status": "forbidden_unit_cell", "detail": violation}

    components = _components(vertices, n)
    if not all(_is_straight_interval(component) for component in components):
        return {**record, "status": "nonstraight_component"}
    required_components = [moved_blocker, frozenset((beta,)), frozenset((gamma,))]
    if core:
        required_components.append(core)
    if not all(component in components for component in required_components):
        return {**record, "status": "declared_component_not_exact"}
    if not all(piece in components for piece in geometry["pieces"]):
        return {**record, "status": "split_spine_piece_not_exact"}
    expected_count = len(by_id) + 3 + int(bool(core))
    if len(components) != expected_count:
        return {
            **record,
            "status": "wrong_component_count",
            "expected": expected_count,
            "observed": len(components),
        }

    nodes = _nodes(k)
    old_attachment = _attachment_for_edge(carrier_id, spine_id, nodes)
    piece_supports = {piece: _support(piece, n) for piece in geometry["pieces"]}
    near = next(piece for piece, support in piece_supports.items() if old_attachment in support)
    far = next(piece for piece in geometry["pieces"] if piece != near)
    beta_component, gamma_component = frozenset((beta,)), frozenset((gamma,))
    labels = {
        moved_blocker: blocker_id,
        near: NEAR_ID,
        far: FAR_ID,
        beta_component: BETA_ID,
        gamma_component: GAMMA_ID,
    }
    if core:
        labels[core] = CORE_ID
    used = {blocker_id, spine_id}
    for component in components:
        if component in labels:
            continue
        overlaps = [
            name for name, old in by_id.items()
            if name not in {blocker_id, spine_id} and component & old
        ]
        if len(overlaps) != 1 or overlaps[0] in used:
            return {**record, "status": "noninjective_component_transport"}
        labels[component] = overlaps[0]
        used.add(overlaps[0])
    if len(used) != len(by_id):
        return {**record, "status": "missing_old_component"}

    stars = {component: _forced_star(component, n) for component in components}
    if not all(_is_acyclic(edges) for edges, _ in stars.values()):
        return {**record, "status": "cyclic_interval_star"}
    observed_edges = set()
    attachments = {}
    for left_index, left in enumerate(components):
        for right in components[left_index + 1:]:
            intersection = stars[left][1] & stars[right][1]
            if len(intersection) > 1:
                return {
                    **record,
                    "status": "multiple_star_intersection",
                    "detail": {"left": labels[left], "right": labels[right], "size": len(intersection)},
                }
            if intersection:
                edge = frozenset((labels[left], labels[right]))
                observed_edges.add(edge)
                attachments["|".join(sorted(edge))] = list(next(iter(intersection)))

    base_edges = endpoint._base_edges(list(by_id.values()), n)
    old_blocker_edge = frozenset((blocker_id, nodes[blocker_id]["parent"]))
    expected_retained = set()
    for edge in base_edges - {old_blocker_edge}:
        names = set(edge)
        if spine_id not in names:
            expected_retained.add(edge)
            continue
        other = next(iter(names - {spine_id}))
        attachment = _attachment_for_edge(spine_id, other, nodes)
        owner = NEAR_ID if attachment in stars[near][1] else FAR_ID
        expected_retained.add(frozenset((owner, other)))
    special = {blocker_id, BETA_ID, GAMMA_ID, CORE_ID}
    fixed_observed = {edge for edge in observed_edges if not (set(edge) & special)}
    if fixed_observed != expected_retained:
        return {**record, "status": "retained_parent_edges_changed"}
    path = [carrier_id, BETA_ID]
    if core:
        path.extend((CORE_ID, GAMMA_ID, FAR_ID))
    else:
        path.extend((GAMMA_ID, FAR_ID))
    required_path = {
        frozenset((left, right)) for left, right in zip(path, path[1:])
    }
    path_edges = {
        edge for edge in observed_edges if set(edge) & {BETA_ID, GAMMA_ID, CORE_ID}
    }
    if path_edges != required_path:
        return {**record, "status": "declared_connector_path_fails"}
    blocker_edges = [edge for edge in observed_edges if blocker_id in edge]
    if len(blocker_edges) != 1:
        return {**record, "status": "blocker_owner_not_unique"}
    blocker_attachment = attachments["|".join(sorted(blocker_edges[0]))]
    if blocker_attachment == nodes[blocker_id]["physical_parent_attachment"]:
        return {**record, "status": "old_blocker_attachment_not_removed"}
    if len(observed_edges) != len(components) - 1:
        return {**record, "status": "incidence_not_tree_by_edge_count"}
    forest_ok, reason = forest_completion_check(_rows(vertices, n))
    if not forest_ok:
        return {**record, "status": "forced_graph_not_forest", "detail": reason}
    blocker_parent = next(iter(set(blocker_edges[0]) - {blocker_id}))
    return {
        **record,
        "status": "realization",
        "blocker_parent": blocker_parent,
        "owners": {
            "alpha": list(old_attachment),
            "beta": attachments["|".join(sorted((carrier_id, BETA_ID)))],
            "gamma": attachments["|".join(sorted((GAMMA_ID, FAR_ID)))],
            "delta": blocker_attachment,
        },
        "preserved_count": len(vertices),
    }


def replay_offset(k: int, choice: dict) -> dict:
    derivation = derive_offset_choices()
    bypass_type = derivation["types"][choice["type_index"]]
    return _evaluate_offset(
        k,
        bypass_type,
        bypass_type["transported_carriers"][k - 7],
        bypass_type["transported_blockers"][k - 7],
        bypass_type["transported_spines"][k - 7],
        choice["offset_side"],
        tuple(choice["beta_signature"]),
        tuple(choice["gamma_signature"]),
    )


def build_report() -> dict:
    derivation = derive_offset_choices()
    owner_summary = {
        str(k): {
            "censuses": 0,
            "beta_candidates": 0,
            "gamma_candidates": 0,
            "ordered_pairs": 0,
            "valid_pairs": 0,
        }
        for k in (7, 8, 9)
    }
    represented = {
        (choice["type_index"], choice["offset_side"]): choice
        for choice in derivation["choices"]
    }
    offset_records = [*derivation["rejected_offsets"], *represented.values()]
    for record in offset_records:
        for census in record["owner_equation_censuses"]:
            summary = owner_summary[str(census["k"])]
            summary["censuses"] += 1
            summary["beta_candidates"] += census["beta_candidate_count"]
            summary["gamma_candidates"] += census["gamma_candidate_count"]
            summary["ordered_pairs"] += census["ordered_pair_attempts"]
            summary["valid_pairs"] += len(census["valid_signatures"])
    chains = []
    terminal = Counter()
    width_terminal = {k: Counter() for k in (7, 8, 9)}
    map78, map89 = endpoint._owner_map(7), endpoint._owner_map(8)
    for choice in derivation["choices"]:
        evaluations = [replay_offset(k, choice) for k in (7, 8, 9)]
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
                for field in ("carrier_ray", "offset_core", "moved_blocker")
                for vertex in source[field]
            } | {
                _standard_insertion_image(tuple(source["beta_connector"])),
                _standard_insertion_image(tuple(source["gamma_connector"])),
            }
            target_added = {
                tuple(vertex)
                for field in ("carrier_ray", "offset_core", "moved_blocker")
                for vertex in target[field]
            } | {tuple(target["beta_connector"]), tuple(target["gamma_connector"])}
            source_removed = {
                _standard_insertion_image(tuple(vertex))
                for vertex in source["removed_spine_segment"]
            }
            target_removed = {tuple(vertex) for vertex in target["removed_spine_segment"]}
            coordinate_nesting.append(source_added <= target_added and source_removed <= target_removed)
        parent_stable = False
        if all(item["status"] == "realization" for item in evaluations):
            parent_stable = (
                evaluations[1]["blocker_parent"] == map78[evaluations[0]["blocker_parent"]]
                and evaluations[2]["blocker_parent"] == map89[evaluations[1]["blocker_parent"]]
            )
        stable = all(item["status"] == "realization" for item in evaluations)
        stable &= all(coordinate_nesting) and parent_stable
        chains.append({
            "choice": choice,
            "width_evaluations": evaluations,
            "coordinate_images_nest": coordinate_nesting,
            "blocker_parent_transports": parent_stable,
            "status": "stable_realization" if stable else "obstructed",
        })
    survivors = [chain for chain in chains if chain["status"] == "stable_realization"]
    return {
        "schema": SCHEMA,
        "checker": "residue_two_offset_spine_bypass_census",
        "status": "stable_realization" if survivors else "complete_offset_spine_bypass_obstruction",
        "grammar": {
            "source_types": len(derivation["types"]),
            "offset_sides_per_type": list(OFFSET_SIDES),
            "offset_attempts": derivation["offset_attempts"],
            "connector_local_box": {
                "x": [min(LOCAL_X_RANGE), max(LOCAL_X_RANGE)],
                "y": [min(LOCAL_Y_RANGE), max(LOCAL_Y_RANGE)],
            },
            "transported_connector_choices": len(derivation["choices"]),
            "other_edits": "none",
        },
        "derivation": derivation,
        "owner_equation_summary": owner_summary,
        "terminal_histogram": dict(sorted(terminal.items())),
        "width_terminal_histograms": {
            str(k): dict(sorted(values.items())) for k, values in width_terminal.items()
        },
        "chains": chains,
        "survivors": survivors,
        "next_topology": {
            "name": "borrowed-leaf offset bypass",
            "specification": (
                "restore an equal-length k-5 offset core and translate the prescribed blocker "
                "plus one witness-named affine leaf into the beta and gamma connector roles, "
                "instead of adding connector centers"
            ),
            "count": (
                "remove k-5 spine centers and add k-5 core centers; two leaf translations are "
                "zero-net; carrier contributes the target correction"
            ),
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
