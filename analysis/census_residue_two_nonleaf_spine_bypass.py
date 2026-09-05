#!/usr/bin/env python3
"""Exhaust witness-derived nonleaf-spine split bypasses."""

from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path

import census_residue_two_affine_endpoint_extensions as endpoint
from census_residue_two_counter_interval_geometry import _local_cell_violation, _rows
from census_residue_two_endpoint_slide import _translate
from check_residue_two_affine_interval_skeleton import (
    _components,
    _forced_star,
    _interval_id,
    _interval_key,
    _is_acyclic,
    _is_straight_interval,
    _standard_insertion_image,
    analyze_k,
)
from construction_lab import forest_completion_check


Vertex = tuple[int, int]
SCHEMA = "grid-graphs.residue-two-nonleaf-spine-bypass-census.v1"
SOURCE_ARTIFACT = Path(__file__).with_name("residue_two_two_leaf_hinge_census.json")
BYPASS_ID = "S:bypass"
NEAR_ID = "S:near"
FAR_ID = "S:far"


def _nodes(k: int) -> dict[str, dict]:
    return {
        node["id"]: node
        for node in analyze_k(k)["rooted_symbolic_skeleton"]["nodes"]
    }


def _components_by_id(k: int) -> dict[str, frozenset[Vertex]]:
    return {
        _interval_id(component): component
        for component in _components(endpoint._preserved(k), 3 * k + 2)
    }


def _transported(source: str) -> tuple[str, str, str]:
    map78, map89 = endpoint._owner_map(7), endpoint._owner_map(8)
    middle = map78[source]
    return source, middle, map89[middle]


def derive_bypass_types(source_artifact: Path = SOURCE_ARTIFACT) -> list[dict]:
    """Turn exactly the five excluded non-leaf hinges into split types."""
    source = json.loads(source_artifact.read_text())
    excluded = source["derivation"]["excluded_witnesses"]
    result = []
    for witness in excluded:
        rejected = witness["rejected"]
        if len(rejected) != 1:
            raise ValueError("each excluded witness must name exactly one non-leaf spine")
        spine = rejected[0]["hinge"]
        carrier, blocker = witness["carrier"], witness["blocker"]
        carrier_names = _transported(carrier)
        blocker_names = _transported(blocker)
        spine_names = _transported(spine)
        old_interfaces = []
        for k, moved_carrier, moved_blocker, moved_spine in zip(
            (7, 8, 9), carrier_names, blocker_names, spine_names
        ):
            nodes = _nodes(k)
            carrier_spine_child = (
                moved_carrier if nodes[moved_carrier]["parent"] == moved_spine
                else moved_spine if nodes[moved_spine]["parent"] == moved_carrier
                else None
            )
            if carrier_spine_child is None:
                raise ValueError("named carrier and spine do not have an old parent edge")
            old_interfaces.append({
                "k": k,
                "blocker_parent_edge": [nodes[moved_blocker]["parent"], moved_blocker],
                "blocker_attachment": nodes[moved_blocker]["physical_parent_attachment"],
                "carrier_spine_edge": [moved_carrier, moved_spine],
                "carrier_spine_attachment": nodes[carrier_spine_child]["physical_parent_attachment"],
                "spine_parent": nodes[moved_spine]["parent"],
            })
        result.append({
            "source_chain_index": witness["source_chain_index"],
            "carrier": carrier,
            "side": witness["side"],
            "blocker": blocker,
            "spine": spine,
            "blocker_translation": witness["rigid_translation"],
            "transported_carriers": list(carrier_names),
            "transported_blockers": list(blocker_names),
            "transported_spines": list(spine_names),
            "old_interfaces": old_interfaces,
            "removed_segment_rule": "orthogonal projection of the carrier ray onto the spine",
            "bypass_rule": (
                "from the far projected endpoint, k-5 centers perpendicular toward the carrier"
            ),
            "declared_singleton_owners": [
                "alpha_k(near spine, carrier): retained old owner",
                "beta_k(carrier, bypass)",
                "gamma_k(bypass, far spine)",
                "delta_k(translated blocker, replacement parent)",
            ],
        })
    return result


def _split_geometry(
    k: int, carrier: frozenset[Vertex], side: str, spine: frozenset[Vertex]
) -> dict:
    length = k - 5
    ray = endpoint._ray(carrier, side, length)
    carrier_orientation, carrier_fixed, _, _ = _interval_key(carrier)
    spine_orientation, spine_fixed, spine_start, spine_end = _interval_key(spine)
    if carrier_orientation != spine_orientation:
        raise ValueError("witness carrier and spine must be parallel")
    moving_values = sorted(column if carrier_orientation == "H" else row for row, column in ray)
    removed = frozenset(
        (spine_fixed, value) if spine_orientation == "H" else (value, spine_fixed)
        for value in moving_values
    )
    if not removed <= spine:
        raise ValueError("carrier projection is not contained in the named spine")
    far = moving_values[-1] if side == "end" else moving_values[0]
    direction = 1 if spine_fixed < carrier_fixed else -1
    bypass = frozenset(
        (spine_fixed + direction * offset, far)
        if spine_orientation == "H"
        else (far, spine_fixed + direction * offset)
        for offset in range(1, length + 1)
    )
    pieces = _components(set(spine - removed), 3 * k + 2)
    if len(pieces) != 2 or not all(_is_straight_interval(piece) for piece in pieces):
        raise ValueError("projection does not split the spine into exactly two intervals")
    return {
        "ray": ray,
        "removed": removed,
        "bypass": bypass,
        "pieces": pieces,
        "far_moving_coordinate": far,
        "perpendicular_direction": direction,
    }


def _attachment_for_edge(left: str, right: str, nodes: dict[str, dict]) -> Vertex:
    if nodes[left]["parent"] == right:
        return tuple(nodes[left]["physical_parent_attachment"])
    if nodes[right]["parent"] == left:
        return tuple(nodes[right]["physical_parent_attachment"])
    raise ValueError("edge is not a rooted parent edge")


def _evaluate_bypass(
    k: int,
    carrier_id: str,
    side: str,
    blocker_id: str,
    spine_id: str,
    blocker_delta: Vertex,
) -> dict:
    n = 3 * k + 2
    base = endpoint._preserved(k)
    by_id = _components_by_id(k)
    carrier, blocker, spine = by_id[carrier_id], by_id[blocker_id], by_id[spine_id]
    geometry = _split_geometry(k, carrier, side, spine)
    ray = geometry["ray"]
    moved_blocker = _translate(blocker, blocker_delta)
    removed, bypass = geometry["removed"], geometry["bypass"]
    record = {
        "k": k,
        "carrier": carrier_id,
        "side": side,
        "blocker": blocker_id,
        "spine": spine_id,
        "blocker_translation": list(blocker_delta),
        "carrier_ray": [list(vertex) for vertex in sorted(ray)],
        "removed_spine_segment": [list(vertex) for vertex in sorted(removed)],
        "perpendicular_bypass": [list(vertex) for vertex in sorted(bypass)],
        "spine_pieces": [
            [list(vertex) for vertex in sorted(piece)] for piece in geometry["pieces"]
        ],
        "far_moving_coordinate": geometry["far_moving_coordinate"],
        "perpendicular_direction": geometry["perpendicular_direction"],
    }
    if not all(
        0 <= row < n and 0 <= column < n
        for row, column in ray | moved_blocker | bypass
    ):
        return {**record, "status": "bypass_out_of_grid"}
    vertices = (base - blocker - removed) | set(moved_blocker) | set(ray) | set(bypass)
    target = 3 * k * k + 7 * k
    if len(vertices) != target:
        overlap = (set(ray) | set(moved_blocker) | set(bypass)) & (base - blocker - removed)
        overlap |= (set(ray) & set(bypass)) | (set(moved_blocker) & (set(ray) | set(bypass)))
        return {
            **record,
            "status": "wrong_target_count_due_to_overlap",
            "expected": target,
            "observed": len(vertices),
            "overlap": [list(vertex) for vertex in sorted(overlap)],
        }
    violation = _local_cell_violation(
        vertices, set(blocker) | set(moved_blocker) | set(removed) | set(ray) | set(bypass), n
    )
    if violation is not None:
        return {**record, "status": "forbidden_unit_cell", "detail": violation}

    components = _components(vertices, n)
    if not all(_is_straight_interval(component) for component in components):
        return {**record, "status": "nonstraight_component"}
    if bypass not in components or moved_blocker not in components:
        return {**record, "status": "bypass_or_blocker_not_exact_component"}
    spine_pieces = geometry["pieces"]
    if not all(piece in components for piece in spine_pieces):
        return {**record, "status": "split_spine_piece_not_exact_component"}
    if len(components) != len(by_id) + 2:
        return {
            **record,
            "status": "wrong_component_count",
            "expected": len(by_id) + 2,
            "observed": len(components),
        }

    nodes = _nodes(k)
    old_carrier_attachment = _attachment_for_edge(carrier_id, spine_id, nodes)
    supports_of_pieces = {
        piece: _forced_star(piece, n)[1] for piece in spine_pieces
    }
    near_candidates = [
        piece for piece, support in supports_of_pieces.items()
        if old_carrier_attachment in support
    ]
    if len(near_candidates) != 1:
        return {**record, "status": "old_carrier_owner_not_on_unique_spine_piece"}
    near = near_candidates[0]
    far = next(piece for piece in spine_pieces if piece != near)
    labels = {bypass: BYPASS_ID, moved_blocker: blocker_id, near: NEAR_ID, far: FAR_ID}
    used = {blocker_id, spine_id}
    for component in components:
        if component in labels:
            continue
        overlaps = [
            name for name, old in by_id.items()
            if name not in {blocker_id, spine_id} and component & old
        ]
        if len(overlaps) != 1 or overlaps[0] in used:
            return {**record, "status": "noninjective_component_transport", "detail": overlaps}
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
                    "detail": {
                        "left": labels[left],
                        "right": labels[right],
                        "size": len(intersection),
                    },
                }
            if intersection:
                edge = frozenset((labels[left], labels[right]))
                observed_edges.add(edge)
                attachments["|".join(sorted(edge))] = list(next(iter(intersection)))

    base_components = list(by_id.values())
    base_edges = endpoint._base_edges(base_components, n)
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

    special_names = {BYPASS_ID, blocker_id}
    fixed_observed = {
        edge for edge in observed_edges if not (set(edge) & special_names)
    }
    if fixed_observed != expected_retained:
        return {**record, "status": "retained_parent_edges_changed"}
    required_bypass_edges = {
        frozenset((carrier_id, BYPASS_ID)),
        frozenset((BYPASS_ID, FAR_ID)),
    }
    bypass_edges = {edge for edge in observed_edges if BYPASS_ID in edge}
    if bypass_edges != required_bypass_edges:
        return {
            **record,
            "status": "declared_bypass_reconnections_fail",
            "observed": [sorted(edge) for edge in sorted(bypass_edges, key=sorted)],
        }
    blocker_edges = [edge for edge in observed_edges if blocker_id in edge]
    if len(blocker_edges) != 1:
        return {**record, "status": "translated_blocker_owner_not_unique"}
    blocker_attachment = attachments["|".join(sorted(blocker_edges[0]))]
    if blocker_attachment == nodes[blocker_id]["physical_parent_attachment"]:
        return {**record, "status": "old_blocker_attachment_not_removed"}

    if len(observed_edges) != len(components) - 1:
        return {**record, "status": "incidence_graph_not_tree_by_edge_count"}
    forest_ok, reason = forest_completion_check(_rows(vertices, n))
    if not forest_ok:
        return {**record, "status": "forced_graph_not_forest", "detail": reason}
    blocker_parent = next(iter(set(blocker_edges[0]) - {blocker_id}))
    return {
        **record,
        "status": "realization",
        "retained_owner_alpha": list(old_carrier_attachment),
        "replacement_owner_beta": attachments["|".join(sorted((carrier_id, BYPASS_ID)))],
        "replacement_owner_gamma": attachments["|".join(sorted((BYPASS_ID, FAR_ID)))],
        "blocker_owner_delta": blocker_attachment,
        "blocker_parent": blocker_parent,
        "preserved_count": len(vertices),
    }


def replay_bypass(
    k: int,
    carrier: str,
    side: str,
    blocker: str,
    spine: str,
    blocker_delta: Vertex,
) -> dict:
    return _evaluate_bypass(k, carrier, side, blocker, spine, blocker_delta)


def build_report(source_artifact: Path = SOURCE_ARTIFACT) -> dict:
    types = derive_bypass_types(source_artifact)
    map78, map89 = endpoint._owner_map(7), endpoint._owner_map(8)
    chains = []
    terminal = Counter()
    width_terminal = {k: Counter() for k in (7, 8, 9)}
    for bypass_type in types:
        delta = tuple(bypass_type["blocker_translation"])
        evaluations = [
            _evaluate_bypass(k, carrier, bypass_type["side"], blocker, spine, delta)
            for k, carrier, blocker, spine in zip(
                (7, 8, 9),
                bypass_type["transported_carriers"],
                bypass_type["transported_blockers"],
                bypass_type["transported_spines"],
            )
        ]
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
                for field in ("carrier_ray", "perpendicular_bypass")
                for vertex in source[field]
            }
            target_added = {
                tuple(vertex)
                for field in ("carrier_ray", "perpendicular_bypass")
                for vertex in target[field]
            }
            source_removed = {
                _standard_insertion_image(tuple(vertex))
                for vertex in source["removed_spine_segment"]
            }
            target_removed = {tuple(vertex) for vertex in target["removed_spine_segment"]}
            coordinate_nesting.append(
                source_added <= target_added and source_removed <= target_removed
            )
        parent_stable = False
        if all(item["status"] == "realization" for item in evaluations):
            parent_stable = (
                evaluations[1]["blocker_parent"] == map78[evaluations[0]["blocker_parent"]]
                and evaluations[2]["blocker_parent"] == map89[evaluations[1]["blocker_parent"]]
            )
        stable = all(item["status"] == "realization" for item in evaluations)
        stable &= all(coordinate_nesting) and parent_stable
        chains.append({
            "type": bypass_type,
            "width_evaluations": evaluations,
            "coordinate_images_nest": coordinate_nesting,
            "blocker_parent_transports": parent_stable,
            "status": "stable_realization" if stable else "obstructed",
        })
    survivors = [chain for chain in chains if chain["status"] == "stable_realization"]
    return {
        "schema": SCHEMA,
        "checker": "residue_two_nonleaf_spine_bypass_census",
        "source_artifact": source_artifact.name,
        "status": "stable_realization" if survivors else "complete_nonleaf_spine_bypass_obstruction",
        "grammar": {
            "source_nonleaf_witnesses": len(types),
            "choices_per_witness": 1,
            "chain_count": len(chains),
            "other_edits": "none",
            "split": "carrier-ray orthogonal projection on named spine",
            "bypass": "equal length, far endpoint, perpendicular toward carrier",
        },
        "types": types,
        "terminal_histogram": dict(sorted(terminal.items())),
        "width_terminal_histograms": {
            str(k): dict(sorted(values.items())) for k, values in width_terminal.items()
        },
        "chains": chains,
        "survivors": survivors,
        "next_topology": {
            "name": "offset spine bypass",
            "specification": (
                "retain the same projected spine split, but place the equal-length bypass one "
                "additional lattice layer away so it meets carrier and far spine only through "
                "two short singleton connector leaves"
            ),
            "count": (
                "spine relocation 0; blocker translation 0; two connector leaves must be paid "
                "by shortening the bypass by two; carrier remains +1 per step"
            ),
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=SOURCE_ARTIFACT)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    payload = json.dumps(build_report(args.source), indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(payload)
    else:
        print(payload, end="")


if __name__ == "__main__":
    main()
