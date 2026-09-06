#!/usr/bin/env python3
"""Exhaust the derived two-interval endpoint-slide grammar."""

from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path

from analysis.residue_geometry import census_residue_two_affine_endpoint_extensions as endpoint
from analysis.residue_geometry.census_residue_two_counter_interval_geometry import _local_cell_violation, _rows
from analysis.residue_geometry.check_residue_two_affine_interval_skeleton import (
    _components,
    _forced_star,
    _interval_id,
    _is_acyclic,
    _is_straight_interval,
    _standard_insertion_image,
    analyze_k,
)
from analysis.patterns.construction_lab import forest_completion_check


Vertex = tuple[int, int]
SCHEMA = "grid-graphs.residue-two-endpoint-slide-census.v1"
TRANSLATIONS = ((-1, 0), (0, -1), (0, 1), (1, 0))


def _translate(component: frozenset[Vertex], delta: Vertex) -> frozenset[Vertex]:
    dr, dc = delta
    return frozenset((row + dr, column + dc) for row, column in component)


def _adjacent(component: frozenset[Vertex], vertices: set[Vertex]) -> bool:
    return any(
        abs(row - other_row) + abs(column - other_column) == 1
        for row, column in component
        for other_row, other_column in vertices
    )


def _blockers_from_first_obstruction(
    carrier: str,
    ray: set[Vertex],
    obstruction: dict,
    components: dict[str, frozenset[Vertex]],
) -> set[str]:
    status = obstruction["status"]
    if status == "ray_contains_old_preserved_vertex":
        return {name for name, component in components.items() if component & ray}
    if status == "forbidden_unit_cell":
        row, column = obstruction["detail"]["cell"]
        old_cells = {
            (row + dr, column + dc)
            for dr, dc in map(tuple, obstruction["detail"]["preserved_offsets"])
        } - ray
        return {
            name for name, component in components.items()
            if name != carrier and component & old_cells
        }
    if status == "component_merge_or_split":
        return {
            name for name, component in components.items()
            if name != carrier and _adjacent(component, ray)
        }
    return set()


def derive_pair_types() -> list[dict]:
    """Derive, rather than search for, constant-size leaf blockers at k=7."""
    components_by_k = {
        k: {
            _interval_id(component): component
            for component in _components(endpoint._preserved(k), 3 * k + 2)
        }
        for k in (7, 8, 9)
    }
    nodes_by_k = {
        k: {
            node["id"]: node
            for node in analyze_k(k)["rooted_symbolic_skeleton"]["nodes"]
        }
        for k in (7, 8, 9)
    }
    map78, map89 = endpoint._owner_map(7), endpoint._owner_map(8)
    pairs = []
    for carrier, component in components_by_k[7].items():
        for side in ("start", "end"):
            obstruction = endpoint._evaluate(7, carrier, side)
            ray = set(map(tuple, obstruction["ray"]))
            blockers = _blockers_from_first_obstruction(
                carrier, ray, obstruction, components_by_k[7]
            )
            for blocker in sorted(blockers):
                blocker8, blocker9 = map78[blocker], map89[map78[blocker]]
                transported = (blocker, blocker8, blocker9)
                lengths = tuple(
                    len(components_by_k[k][name])
                    for k, name in zip((7, 8, 9), transported)
                )
                if len(set(lengths)) != 1:
                    continue
                if not all(
                    not nodes_by_k[k][name]["children"]
                    for k, name in zip((7, 8, 9), transported)
                ):
                    continue
                pairs.append({
                    "carrier": carrier,
                    "side": side,
                    "first_obstruction": obstruction["status"],
                    "blocker": blocker,
                    "blocker_length": lengths[0],
                    "transported_blockers": list(transported),
                })
    return pairs


def _evaluate_slide(
    k: int, carrier: str, side: str, blocker: str, delta: Vertex
) -> dict:
    n = 3 * k + 2
    base = endpoint._preserved(k)
    base_components = _components(base, n)
    by_id = {_interval_id(component): component for component in base_components}
    carrier_component, blocker_component = by_id[carrier], by_id[blocker]
    ray = endpoint._ray(carrier_component, side, k - 5)
    moved_blocker = _translate(blocker_component, delta)
    record = {
        "k": k,
        "carrier": carrier,
        "side": side,
        "blocker": blocker,
        "translation": list(delta),
        "carrier_ray": [list(vertex) for vertex in sorted(ray)],
        "translated_blocker": [list(vertex) for vertex in sorted(moved_blocker)],
    }
    if not all(
        0 <= row < n and 0 <= column < n
        for row, column in ray | moved_blocker
    ):
        return {**record, "status": "translated_geometry_out_of_grid"}

    vertices = (base - blocker_component) | set(ray) | set(moved_blocker)
    if len(vertices) != 3 * k * k + 7 * k:
        return {
            **record,
            "status": "wrong_target_count_due_to_overlap",
            "expected": 3 * k * k + 7 * k,
            "observed": len(vertices),
        }
    violation = _local_cell_violation(
        vertices, set(ray) | set(blocker_component) | set(moved_blocker), n
    )
    if violation is not None:
        return {**record, "status": "forbidden_unit_cell", "detail": violation}

    components = _components(vertices, n)
    if not all(_is_straight_interval(component) for component in components):
        return {**record, "status": "nonstraight_component"}
    if moved_blocker not in components:
        return {**record, "status": "translated_blocker_not_exact_component"}
    if len(components) != len(base_components):
        return {
            **record,
            "status": "wrong_component_count",
            "expected": len(base_components),
            "observed": len(components),
        }

    labels = {moved_blocker: blocker}
    used = {blocker}
    for component in components:
        if component == moved_blocker:
            continue
        overlaps = [
            name for name, old in by_id.items()
            if name != blocker and component & old
        ]
        if len(overlaps) != 1 or overlaps[0] in used:
            return {
                **record,
                "status": "noninjective_component_transport",
                "detail": overlaps,
            }
        labels[component] = overlaps[0]
        used.add(overlaps[0])
    if len(used) != len(base_components):
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

    nodes = {
        node["id"]: node
        for node in analyze_k(k)["rooted_symbolic_skeleton"]["nodes"]
    }
    old_parent = nodes[blocker]["parent"]
    old_attachment = nodes[blocker]["physical_parent_attachment"]
    base_edges = endpoint._base_edges(base_components, n)
    old_edge = frozenset((blocker, old_parent))
    fixed_edges = {edge for edge in observed_edges if blocker not in edge}
    if fixed_edges != base_edges - {old_edge}:
        return {
            **record,
            "status": "nonblocker_parent_tree_changed",
            "detail": {
                "missing": [
                    sorted(edge) for edge in sorted((base_edges - {old_edge}) - fixed_edges, key=sorted)
                ],
                "extra": [
                    sorted(edge) for edge in sorted(fixed_edges - (base_edges - {old_edge}), key=sorted)
                ],
            },
        }
    blocker_edges = [edge for edge in observed_edges if blocker in edge]
    if len(blocker_edges) != 1:
        return {
            **record,
            "status": "translated_blocker_not_leaf",
            "observed_degree": len(blocker_edges),
        }
    new_edge = blocker_edges[0]
    new_attachment = attachments["|".join(sorted(new_edge))]
    if new_attachment == old_attachment:
        return {**record, "status": "old_attachment_not_removed"}

    forest_ok, reason = forest_completion_check(_rows(vertices, n))
    if not forest_ok:
        return {**record, "status": "forced_graph_not_forest", "detail": reason}
    new_parent = next(iter(new_edge - {blocker}))
    return {
        **record,
        "status": "realization",
        "old_parent": old_parent,
        "old_attachment": old_attachment,
        "new_parent": new_parent,
        "new_attachment": new_attachment,
        "preserved_count": len(vertices),
    }


def replay_slide(k: int, carrier: str, side: str, blocker: str, delta: Vertex) -> dict:
    return _evaluate_slide(k, carrier, side, blocker, delta)


def build_report() -> dict:
    pairs = derive_pair_types()
    map78, map89 = endpoint._owner_map(7), endpoint._owner_map(8)
    chains = []
    terminal = Counter()
    width_terminal = {k: Counter() for k in (7, 8, 9)}
    for pair in pairs:
        carrier7 = pair["carrier"]
        carriers = (carrier7, map78[carrier7], map89[map78[carrier7]])
        blockers = tuple(pair["transported_blockers"])
        for delta in TRANSLATIONS:
            evaluations = [
                _evaluate_slide(k, carrier, pair["side"], blocker, delta)
                for k, carrier, blocker in zip((7, 8, 9), carriers, blockers)
            ]
            for evaluation in evaluations:
                width_terminal[evaluation["k"]][evaluation["status"]] += 1
            first_failure = next(
                (item["status"] for item in evaluations if item["status"] != "realization"),
                "realization",
            )
            terminal[first_failure] += 1
            moved_nesting = []
            ray_nesting = []
            for source, target in zip(evaluations, evaluations[1:]):
                moved_nesting.append({
                    _standard_insertion_image(tuple(vertex))
                    for vertex in source["translated_blocker"]
                } <= {tuple(vertex) for vertex in target["translated_blocker"]})
                ray_nesting.append({
                    _standard_insertion_image(tuple(vertex))
                    for vertex in source["carrier_ray"]
                } <= {tuple(vertex) for vertex in target["carrier_ray"]})
            parent_map_transports = False
            if all(item["status"] == "realization" for item in evaluations):
                parent_map_transports = (
                    evaluations[1]["new_parent"] == map78[evaluations[0]["new_parent"]]
                    and evaluations[2]["new_parent"] == map89[evaluations[1]["new_parent"]]
                )
            stable = all(item["status"] == "realization" for item in evaluations)
            stable &= all(moved_nesting) and all(ray_nesting) and parent_map_transports
            chains.append({
                "pair": pair,
                "transported_carriers": list(carriers),
                "translation": list(delta),
                "width_evaluations": evaluations,
                "carrier_ray_coordinate_images_nest": ray_nesting,
                "translated_blocker_coordinate_images_nest": moved_nesting,
                "new_parent_map_transports": parent_map_transports,
                "status": "stable_realization" if stable else "obstructed",
            })
    survivors = [chain for chain in chains if chain["status"] == "stable_realization"]
    return {
        "schema": SCHEMA,
        "checker": "residue_two_endpoint_slide_census",
        "status": "stable_realization" if survivors else "complete_endpoint_slide_obstruction",
        "grammar": {
            "pair_derivation": (
                "blockers exactly meet an occupied ray, contribute an old vertex to its first "
                "forbidden cell, or are adjacent components merged by the ray"
            ),
            "blocker_filter": "leaf at k=7,8,9 with one constant length",
            "pair_count": len(pairs),
            "translations": [list(delta) for delta in TRANSLATIONS],
            "chain_count": len(chains),
            "other_edits": "none",
        },
        "derived_pairs": pairs,
        "terminal_histogram": dict(sorted(terminal.items())),
        "width_terminal_histograms": {
            str(k): dict(sorted(histogram.items()))
            for k, histogram in width_terminal.items()
        },
        "chains": chains,
        "survivors": survivors,
        "next_topology": {
            "name": "two-leaf hinge exchange",
            "specification": (
                "move the blocker leaf and one adjacent hinge leaf as a rigid constant-size pair, "
                "then lengthen the carrier and reattach the pair by one singleton owner"
            ),
            "count": "carrier +1 per step; rigid two-leaf translation 0",
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
