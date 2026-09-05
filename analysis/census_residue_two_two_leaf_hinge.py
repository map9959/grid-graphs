#!/usr/bin/env python3
"""Exhaust two-leaf hinge exchanges derived from endpoint-slide witnesses."""

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
    _is_acyclic,
    _is_straight_interval,
    _standard_insertion_image,
    analyze_k,
)
from construction_lab import forest_completion_check


Vertex = tuple[int, int]
SCHEMA = "grid-graphs.residue-two-two-leaf-hinge-census.v1"
SOURCE_ARTIFACT = Path(__file__).with_name("residue_two_endpoint_slide_census.json")
WITNESS_STATUSES = {"multiple_star_intersection", "nonblocker_parent_tree_changed"}


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


def _transported_names(source: str) -> tuple[str, str, str]:
    map78, map89 = endpoint._owner_map(7), endpoint._owner_map(8)
    middle = map78[source]
    return source, middle, map89[middle]


def _leaf_chain(source: str) -> tuple[bool, str]:
    names = _transported_names(source)
    nodes = {k: _nodes(k) for k in (7, 8, 9)}
    components = {k: _components_by_id(k) for k in (7, 8, 9)}
    if not all(not nodes[k][name]["children"] for k, name in zip((7, 8, 9), names)):
        return False, "named hinge is not a leaf at every width"
    lengths = [len(components[k][name]) for k, name in zip((7, 8, 9), names)]
    if len(set(lengths)) != 1:
        return False, "named hinge does not have constant length"
    return True, "transported constant-size leaf"


def derive_hinge_types(source_artifact: Path = SOURCE_ARTIFACT) -> dict:
    """Derive the minimal hinge from each of the seven terminal witnesses."""
    payload = json.loads(source_artifact.read_text())
    derived = []
    excluded = []
    for chain_index, chain in enumerate(payload["chains"]):
        failure = chain["width_evaluations"][0]
        if failure["status"] not in WITNESS_STATUSES:
            continue
        pair = chain["pair"]
        carrier, blocker = pair["carrier"], pair["blocker"]
        if failure["status"] == "multiple_star_intersection":
            names = {failure["detail"]["left"], failure["detail"]["right"]}
            hinges = sorted(names - {carrier, blocker})
            derivation = "non-carrier/non-blocker member of the multiple intersection"
        else:
            changed_edges = failure["detail"]["missing"] + failure["detail"]["extra"]
            hinges = sorted({
                name
                for edge in changed_edges
                for name in edge
                if name not in {carrier, blocker}
            })
            derivation = "leaf endpoint of a changed non-blocker edge adjacent to the carrier"
        eligible = []
        rejected = []
        for hinge in hinges:
            ok, reason = _leaf_chain(hinge)
            (eligible if ok else rejected).append({"hinge": hinge, "reason": reason})
        witness = {
            "source_chain_index": chain_index,
            "failure_status": failure["status"],
            "carrier": carrier,
            "side": pair["side"],
            "blocker": blocker,
            "rigid_translation": chain["translation"],
            "hinge_derivation": derivation,
            "named_hinges": hinges,
        }
        if len(eligible) == 1:
            hinge = eligible[0]["hinge"]
            transported_blockers = _transported_names(blocker)
            transported_hinges = _transported_names(hinge)
            old_parent_edges = []
            for k, moved_blocker, moved_hinge in zip(
                (7, 8, 9), transported_blockers, transported_hinges
            ):
                nodes = _nodes(k)
                old_parent_edges.append({
                    "k": k,
                    "edges": [
                        [nodes[moved_blocker]["parent"], moved_blocker],
                        [nodes[moved_hinge]["parent"], moved_hinge],
                    ],
                    "attachments": [
                        nodes[moved_blocker]["physical_parent_attachment"],
                        nodes[moved_hinge]["physical_parent_attachment"],
                    ],
                })
            derived.append({
                **witness,
                "hinge": hinge,
                "transported_carriers": list(_transported_names(carrier)),
                "transported_blockers": list(transported_blockers),
                "transported_hinges": list(transported_hinges),
                "old_parent_edges": old_parent_edges,
                "replacement_singleton_owner": "gamma_k(external parent, moved hinge pair)",
            })
        else:
            excluded.append({
                **witness,
                "eligible": eligible,
                "rejected": rejected,
                "reason": "witness does not name exactly one transported constant-size leaf hinge",
            })
    return {
        "source_witness_count": len(derived) + len(excluded),
        "derived_types": derived,
        "excluded_witnesses": excluded,
    }


def _evaluate_hinge(
    k: int,
    carrier: str,
    side: str,
    blocker: str,
    hinge: str,
    delta: Vertex,
) -> dict:
    n = 3 * k + 2
    base = endpoint._preserved(k)
    by_id = _components_by_id(k)
    carrier_component = by_id[carrier]
    blocker_component, hinge_component = by_id[blocker], by_id[hinge]
    ray = endpoint._ray(carrier_component, side, k - 5)
    moved_blocker = _translate(blocker_component, delta)
    moved_hinge = _translate(hinge_component, delta)
    record = {
        "k": k,
        "carrier": carrier,
        "side": side,
        "blocker": blocker,
        "hinge": hinge,
        "rigid_translation": list(delta),
        "carrier_ray": [list(vertex) for vertex in sorted(ray)],
        "moved_blocker": [list(vertex) for vertex in sorted(moved_blocker)],
        "moved_hinge": [list(vertex) for vertex in sorted(moved_hinge)],
    }
    moved = moved_blocker | moved_hinge
    if not all(0 <= row < n and 0 <= column < n for row, column in ray | moved):
        return {**record, "status": "translated_geometry_out_of_grid"}
    vertices = (base - blocker_component - hinge_component) | set(ray) | set(moved)
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
        set(ray) | set(blocker_component) | set(hinge_component) | set(moved),
        n,
    )
    if violation is not None:
        return {**record, "status": "forbidden_unit_cell", "detail": violation}

    components = _components(vertices, n)
    if not all(_is_straight_interval(component) for component in components):
        return {**record, "status": "nonstraight_component"}
    if moved_blocker not in components or moved_hinge not in components:
        return {**record, "status": "moved_leaf_not_exact_component"}
    if len(components) != len(by_id):
        return {
            **record,
            "status": "wrong_component_count",
            "expected": len(by_id),
            "observed": len(components),
        }

    labels = {moved_blocker: blocker, moved_hinge: hinge}
    used = {blocker, hinge}
    for component in components:
        if component in labels:
            continue
        overlaps = [
            name for name, old in by_id.items()
            if name not in {blocker, hinge} and component & old
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

    nodes = _nodes(k)
    old_edges = {
        frozenset((blocker, nodes[blocker]["parent"])),
        frozenset((hinge, nodes[hinge]["parent"])),
    }
    base_edges = endpoint._base_edges(list(by_id.values()), n)
    pair_names = {blocker, hinge}
    fixed_observed = {
        edge for edge in observed_edges if not (set(edge) & pair_names)
    }
    fixed_expected = base_edges - old_edges
    if fixed_observed != fixed_expected:
        return {**record, "status": "fixed_parent_tree_changed"}
    pair_edges = [edge for edge in observed_edges if set(edge) & pair_names]
    internal = frozenset((blocker, hinge))
    if internal not in pair_edges:
        return {**record, "status": "moved_pair_not_hinged"}
    external = [edge for edge in pair_edges if edge != internal]
    if len(external) != 1 or len(set(external[0]) & pair_names) != 1:
        return {
            **record,
            "status": "replacement_owner_not_unique",
            "observed_pair_edge_count": len(pair_edges),
        }
    for leaf in (blocker, hinge):
        old_attachment = nodes[leaf]["physical_parent_attachment"]
        old_parent_edge = frozenset((leaf, nodes[leaf]["parent"]))
        key = "|".join(sorted(old_parent_edge))
        if key in attachments and attachments[key] == old_attachment:
            return {**record, "status": "old_attachment_not_removed", "leaf": leaf}

    forest_ok, reason = forest_completion_check(_rows(vertices, n))
    if not forest_ok:
        return {**record, "status": "forced_graph_not_forest", "detail": reason}
    external_edge = external[0]
    external_parent = next(iter(set(external_edge) - pair_names))
    return {
        **record,
        "status": "realization",
        "old_parent_edges": [sorted(edge) for edge in old_edges],
        "internal_hinge_attachment": attachments["|".join(sorted(internal))],
        "replacement_parent": external_parent,
        "replacement_singleton_owner": attachments["|".join(sorted(external_edge))],
        "preserved_count": len(vertices),
    }


def replay_hinge(
    k: int, carrier: str, side: str, blocker: str, hinge: str, delta: Vertex
) -> dict:
    return _evaluate_hinge(k, carrier, side, blocker, hinge, delta)


def build_report(source_artifact: Path = SOURCE_ARTIFACT) -> dict:
    derivation = derive_hinge_types(source_artifact)
    chains = []
    histogram = Counter()
    width_histograms = {k: Counter() for k in (7, 8, 9)}
    map78, map89 = endpoint._owner_map(7), endpoint._owner_map(8)
    for hinge_type in derivation["derived_types"]:
        delta = tuple(hinge_type["rigid_translation"])
        evaluations = [
            _evaluate_hinge(k, carrier, hinge_type["side"], blocker, hinge, delta)
            for k, carrier, blocker, hinge in zip(
                (7, 8, 9),
                hinge_type["transported_carriers"],
                hinge_type["transported_blockers"],
                hinge_type["transported_hinges"],
            )
        ]
        for evaluation in evaluations:
            width_histograms[evaluation["k"]][evaluation["status"]] += 1
        first_failure = next(
            (item["status"] for item in evaluations if item["status"] != "realization"),
            "realization",
        )
        histogram[first_failure] += 1
        coordinate_nesting = []
        for source, target in zip(evaluations, evaluations[1:]):
            source_extra = {
                _standard_insertion_image(tuple(vertex))
                for field in ("carrier_ray", "moved_blocker", "moved_hinge")
                for vertex in source[field]
            }
            target_extra = {
                tuple(vertex)
                for field in ("carrier_ray", "moved_blocker", "moved_hinge")
                for vertex in target[field]
            }
            coordinate_nesting.append(source_extra <= target_extra)
        parent_transports = False
        if all(item["status"] == "realization" for item in evaluations):
            parent_transports = (
                evaluations[1]["replacement_parent"] == map78[evaluations[0]["replacement_parent"]]
                and evaluations[2]["replacement_parent"] == map89[evaluations[1]["replacement_parent"]]
            )
        stable = all(item["status"] == "realization" for item in evaluations)
        stable &= all(coordinate_nesting) and parent_transports
        chains.append({
            "type": hinge_type,
            "width_evaluations": evaluations,
            "coordinate_images_nest": coordinate_nesting,
            "replacement_parent_transports": parent_transports,
            "status": "stable_realization" if stable else "obstructed",
        })
    survivors = [chain for chain in chains if chain["status"] == "stable_realization"]
    return {
        "schema": SCHEMA,
        "checker": "residue_two_two_leaf_hinge_census",
        "source_artifact": source_artifact.name,
        "status": "stable_realization" if survivors else "complete_two_leaf_hinge_obstruction",
        "grammar": {
            "source_witnesses": derivation["source_witness_count"],
            "derived_hinge_types": len(derivation["derived_types"]),
            "rigid_translations_per_type": 1,
            "chain_count": len(chains),
            "other_edits": "none",
            "replacement_topology": (
                "delete both old leaf-parent edges; require blocker-hinge singleton and exactly "
                "one external singleton gamma_k"
            ),
        },
        "derivation": derivation,
        "terminal_histogram": dict(sorted(histogram.items())),
        "width_terminal_histograms": {
            str(k): dict(sorted(values.items())) for k, values in width_histograms.items()
        },
        "chains": chains,
        "survivors": survivors,
        "next_topology": {
            "name": "nonleaf-spine split bypass",
            "specification": (
                "split the named nonleaf spine at the carrier projection, relocate the removed "
                "segment as a perpendicular bypass of equal size, translate the blocker leaf, "
                "and reconnect the two spine pieces by declared singleton owners"
            ),
            "count": "spine segment relocation 0; blocker translation 0; carrier +1 per step",
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
