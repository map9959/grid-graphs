#!/usr/bin/env python3
"""Census the finite affine endpoint types for an accumulated +1 extension."""

from __future__ import annotations

import argparse
from collections import Counter
from functools import lru_cache
import json
from pathlib import Path

from analysis.residue_geometry.census_residue_two_counter_interval_geometry import (
    _local_cell_violation,
    _rows,
)
from analysis.residue_geometry.check_residue_two_affine_interval_skeleton import (
    _components,
    _forced_star,
    _interval_id,
    _interval_key,
    _is_acyclic,
    _is_straight_interval,
    _standard_insertion_image,
    analyze_transition,
)
from analysis.patterns.construction_lab import forest_completion_check
from analysis.patterns.diagonal_patterns import residue_two_affine_pattern


Vertex = tuple[int, int]
SCHEMA = "grid-graphs.residue-two-affine-endpoint-extension-census.v1"
KS = (7, 8, 9)


def _preserved(k: int) -> set[Vertex]:
    n = 3 * k + 2
    return {
        (row, column)
        for row, values in enumerate(residue_two_affine_pattern(n))
        for column, value in enumerate(values)
        if value == "."
    }


def _ray(component: frozenset[Vertex], side: str, length: int) -> frozenset[Vertex]:
    orientation, fixed, start, end = _interval_key(component)
    moving = (
        range(start - length, start)
        if side == "start"
        else range(end + 1, end + length + 1)
    )
    return frozenset(
        (fixed, value) if orientation == "H" else (value, fixed)
        for value in moving
    )


def _base_edges(
    components: list[frozenset[Vertex]], n: int
) -> set[frozenset[str]]:
    supports = [_forced_star(component, n)[1] for component in components]
    return {
        frozenset((_interval_id(components[left]), _interval_id(components[right])))
        for left in range(len(components))
        for right in range(left + 1, len(components))
        if supports[left] & supports[right]
    }


def _evaluate(k: int, component_id: str, side: str) -> dict:
    n, deficit = 3 * k + 2, k - 5
    base = _preserved(k)
    base_components = _components(base, n)
    by_id = {_interval_id(component): component for component in base_components}
    component = by_id[component_id]
    ray = _ray(component, side, deficit)
    record = {
        "k": k,
        "component": component_id,
        "side": side,
        "extension_length": deficit,
        "ray": [list(vertex) for vertex in sorted(ray)],
    }

    if not all(0 <= row < n and 0 <= column < n for row, column in ray):
        return {**record, "status": "ray_out_of_grid"}
    occupied = sorted(ray & base)
    if occupied:
        return {
            **record,
            "status": "ray_contains_old_preserved_vertex",
            "first_occupied": list(occupied[0]),
        }

    vertices = base | set(ray)
    if len(vertices) != 3 * k * k + 7 * k:
        return {**record, "status": "wrong_target_count", "observed": len(vertices)}
    violation = _local_cell_violation(vertices, set(ray), n)
    if violation is not None:
        return {**record, "status": "forbidden_unit_cell", "detail": violation}

    components = _components(vertices, n)
    if not all(_is_straight_interval(item) for item in components):
        return {**record, "status": "nonstraight_component"}
    if len(components) != len(base_components):
        return {
            **record,
            "status": "component_merge_or_split",
            "expected": len(base_components),
            "observed": len(components),
        }

    labels = {}
    used = set()
    for item in components:
        overlaps = [index for index, old in enumerate(base_components) if item & old]
        if len(overlaps) != 1 or overlaps[0] in used:
            return {
                **record,
                "status": "noninjective_component_transport",
                "overlaps": overlaps,
            }
        index = overlaps[0]
        used.add(index)
        labels[item] = _interval_id(base_components[index])

    stars = {item: _forced_star(item, n) for item in components}
    if not all(_is_acyclic(edges) for edges, _ in stars.values()):
        return {**record, "status": "cyclic_interval_star"}
    observed_edges = set()
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
                        "vertices": [list(vertex) for vertex in sorted(intersection)],
                    },
                }
            if intersection:
                observed_edges.add(frozenset((labels[left], labels[right])))
    expected_edges = _base_edges(base_components, n)
    if observed_edges != expected_edges:
        return {
            **record,
            "status": "parent_tree_changed",
            "detail": {
                "missing": [sorted(edge) for edge in sorted(expected_edges - observed_edges, key=sorted)],
                "extra": [sorted(edge) for edge in sorted(observed_edges - expected_edges, key=sorted)],
            },
        }

    forest_ok, reason = forest_completion_check(_rows(vertices, n))
    if not forest_ok:
        return {**record, "status": "forced_graph_not_forest", "detail": reason}
    return {
        **record,
        "status": "realization",
        "preserved_count": len(vertices),
        "component_count": len(components),
        "incidence_links": len(observed_edges),
    }


@lru_cache(maxsize=3)
def census_k(k: int) -> dict:
    if k not in KS:
        raise ValueError("the endpoint census is declared only at k=7,8,9")
    components = _components(_preserved(k), 3 * k + 2)
    records = [
        _evaluate(k, _interval_id(component), side)
        for component in components
        for side in ("start", "end")
    ]
    histogram = Counter(record["status"] for record in records)
    return {
        "k": k,
        "n": 3 * k + 2,
        "status": "realized" if histogram["realization"] else "all_endpoint_types_obstructed",
        "interval_count": len(components),
        "endpoint_type_count": len(records),
        "terminal_histogram": dict(sorted(histogram.items())),
        "first_replay_by_terminal_status": {
            status: next(record for record in records if record["status"] == status)
            for status in sorted(histogram)
        },
        "records": records,
    }


def _owner_map(k: int) -> dict[str, str]:
    return {
        item["source"]: item["target"]
        for item in analyze_transition(k)["old_nodes"]
    }


def endpoint_chains() -> list[dict]:
    components7 = _components(_preserved(7), 23)
    map78, map89 = _owner_map(7), _owner_map(8)
    chains = []
    for component in components7:
        id7 = _interval_id(component)
        id8 = map78[id7]
        id9 = map89[id8]
        for side in ("start", "end"):
            evaluations = [
                _evaluate(7, id7, side),
                _evaluate(8, id8, side),
                _evaluate(9, id9, side),
            ]
            transition_compatibility = []
            for source, target in zip(evaluations, evaluations[1:]):
                source_images = {
                    _standard_insertion_image(tuple(vertex)) for vertex in source["ray"]
                }
                target_ray = {tuple(vertex) for vertex in target["ray"]}
                transition_compatibility.append(source_images <= target_ray)
            chains.append({
                "source_type": {"component": id7, "side": side},
                "transported_components": [id7, id8, id9],
                "statuses": [item["status"] for item in evaluations],
                "standard_coordinate_images_nest": transition_compatibility,
                "status": (
                    "realization" if all(item["status"] == "realization" for item in evaluations)
                    and all(transition_compatibility)
                    else "obstructed"
                ),
            })
    return chains


def replay_endpoint(k: int, component: str, side: str) -> dict:
    """Replay one serialized endpoint type."""
    return _evaluate(k, component, side)


def build_report() -> dict:
    records = [census_k(k) for k in KS]
    chains = endpoint_chains()
    return {
        "schema": SCHEMA,
        "checker": "residue_two_affine_endpoint_extension_census",
        "status": "complete_endpoint_type_obstruction",
        "abstract_status": (
            "adding k-5 cells to one existing interval has exact target count and would add "
            "one to each affine transition"
        ),
        "geometric_status": "no endpoint type survives even one complete k=7,8,9 family",
        "grammar": {
            "source_types": "the 2 endpoints of each of the 4k audited affine intervals at k=7",
            "type_count": 56,
            "transport": "the checked affine old-node owner maps, retaining start/end side",
            "extension": "the k-5 consecutive collinear cells immediately beyond the endpoint",
            "edits": "add exactly that ray; no deletions, translations, or other additions",
        },
        "width_records": records,
        "transported_endpoint_chains": chains,
        "surviving_chain_count": sum(chain["status"] == "realization" for chain in chains),
        "next_topology": {
            "name": "two-interval endpoint-slide",
            "specification": (
                "lengthen one carrier endpoint by one per step, translate one constant-size "
                "blocking leaf by a zero-net delete/add move, and reparent that leaf through "
                "one declared singleton attachment"
            ),
            "count": "carrier +1; blocker translation 0; total correction +1 per step",
            "reason": (
                "all empty endpoint rays hit a unit-cell obstruction or, at k=7, merge "
                "affine components; a neighboring component must move"
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
