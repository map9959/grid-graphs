#!/usr/bin/env python3
"""Classify the final bounded width-three buffered branch grammar."""

from __future__ import annotations

import argparse
from collections import Counter
import itertools
import json
from pathlib import Path

from analysis.residue_geometry.classify_residue_two_elbow_island import unit_cells_valid
from analysis.residue_geometry.classify_residue_two_staircase_seam import (
    _quadratic_formula,
    cap_maximum,
    forced_forest,
)
from analysis._paths import analysis_path


Vertex = tuple[int, int]
Packet = tuple[int, int, int]
SCHEMA = "grid-graphs.residue-two-buffered-branch.v1"
DEFAULT_OUTPUT = analysis_path("residue_two_buffered_branch.json")
BUFFER_WIDTH = 3


def wall_packets() -> list[Packet]:
    return [packet for packet in itertools.product(range(4), repeat=3) if sum(packet) == 3]


def endpoint_states() -> list[tuple[str, int, int] | None]:
    return [None] + [
        (end, row_offset, buffer_offset)
        for end in ("top", "bottom")
        for row_offset in range(3)
        for buffer_offset in range(1, BUFFER_WIDTH + 1)
    ]


def _base_owned(
    row: int,
    column: int,
    lower: int,
    row_phase: int,
    column_phase: int,
    branch_row: int,
    branch_offset: int,
) -> tuple[bool, str]:
    if column <= lower:
        return column % 3 == column_phase, "exterior"
    if column > lower + BUFFER_WIDTH:
        return row % 3 == row_phase, "exterior"
    return (
        row % 3 == branch_row and column == lower + branch_offset,
        "branch",
    )


def transition_valid(
    row: int,
    lower: int,
    advance: int,
    row_phase: int,
    column_phase: int,
    branch_row: int,
    branch_offset: int,
) -> bool:
    next_lower = lower + advance
    for column in range(min(lower, next_lower) - 2, max(lower, next_lower) + BUFFER_WIDTH + 3):
        present = (
            _base_owned(row, column, lower, row_phase, column_phase,
                        branch_row, branch_offset)[0],
            _base_owned(row, column + 1, lower, row_phase, column_phase,
                        branch_row, branch_offset)[0],
            _base_owned(row + 1, column, next_lower, row_phase, column_phase,
                        branch_row, branch_offset)[0],
            _base_owned(row + 1, column + 1, next_lower, row_phase, column_phase,
                        branch_row, branch_offset)[0],
        )
        if sum(present) >= 3 or present[0] and present[3] or present[1] and present[2]:
            return False
    return True


def local_paths() -> list[dict]:
    paths = []
    for row_phase, column_phase, start, packet, branch_row, branch_offset in itertools.product(
        range(3), range(3), range(3), wall_packets(), range(3), range(1, BUFFER_WIDTH + 1)
    ):
        lower = start
        valid = True
        for row, advance in enumerate(packet):
            if not transition_valid(
                row, lower, advance, row_phase, column_phase, branch_row, branch_offset
            ):
                valid = False
                break
            lower += advance
        if valid:
            paths.append({
                "row_phase": row_phase,
                "column_phase": column_phase,
                "start": start,
                "packet": packet,
                "branch_row": branch_row,
                "branch_offset": branch_offset,
            })
    return paths


def _thresholds(k: int, path: dict) -> list[int]:
    lower = path["start"]
    result = []
    for row in range(3 * k):
        result.append(lower)
        lower += path["packet"][row % 3]
    return result


def connector_vertex(k: int, path: dict, endpoint: tuple[str, int, int] | None) -> Vertex | None:
    if endpoint is None:
        return None
    end, row_offset, buffer_offset = endpoint
    side = 3 * k
    row = row_offset if end == "top" else side - 3 + row_offset
    column = _thresholds(k, path)[row] + buffer_offset
    if not 0 <= column < side:
        return None
    return row + 1, column + 1


def materialize(
    k: int, path: dict, endpoint: tuple[str, int, int] | None
) -> tuple[set[Vertex], set[Vertex], set[Vertex]]:
    side = 3 * k
    thresholds = _thresholds(k, path)
    branch: set[Vertex] = set()
    exterior: set[Vertex] = set()
    for row, lower in enumerate(thresholds):
        for column in range(side):
            keep, owner = _base_owned(
                row,
                column,
                lower,
                path["row_phase"],
                path["column_phase"],
                path["branch_row"],
                path["branch_offset"],
            )
            if keep:
                (branch if owner == "branch" else exterior).add((row + 1, column + 1))
    connector = connector_vertex(k, path, endpoint)
    if connector is not None and connector not in exterior:
        branch.add(connector)
    return branch | exterior, branch, exterior


def _forced_support(n: int, centers: set[Vertex]) -> set[Vertex]:
    support = set(centers)
    for row, column in centers:
        for d_row, d_column in ((-1, 0), (1, 0), (0, -1), (0, 1)):
            neighbor = row + d_row, column + d_column
            if 0 <= neighbor[0] < n and 0 <= neighbor[1] < n:
                support.add(neighbor)
    return support


def articulation_data(n: int, branch: set[Vertex], exterior: set[Vertex]) -> dict:
    intersection = sorted(_forced_support(n, branch) & _forced_support(n, exterior))
    return {
        "intersection_size": len(intersection),
        "singleton": len(intersection) == 1,
        "vertex": list(intersection[0]) if len(intersection) == 1 else None,
    }


def _neighbors(vertex: Vertex, n: int) -> list[Vertex]:
    row, column = vertex
    return [
        (other_row, other_column)
        for other_row, other_column in (
            (row - 1, column), (row + 1, column), (row, column - 1), (row, column + 1)
        )
        if 0 <= other_row < n and 0 <= other_column < n
    ]


def incidence_parent_tree(n: int, preserved: set[Vertex]) -> dict:
    remaining = set(preserved)
    components = []
    while remaining:
        seed = min(remaining)
        remaining.remove(seed)
        component = {seed}
        pending = [seed]
        while pending:
            for neighbor in _neighbors(pending.pop(), n):
                if neighbor in remaining:
                    remaining.remove(neighbor)
                    component.add(neighbor)
                    pending.append(neighbor)
        components.append(frozenset(component))
    supports = [_forced_support(n, set(component)) for component in components]
    links = []
    maximum_intersection = 0
    for left in range(len(components)):
        for right in range(left + 1, len(components)):
            intersection = supports[left] & supports[right]
            maximum_intersection = max(maximum_intersection, len(intersection))
            if intersection:
                links.append((left, right, min(intersection)))
    adjacency = [set() for _ in components]
    for left, right, _ in links:
        adjacency[left].add(right)
        adjacency[right].add(left)
    reached = {0} if components else set()
    pending = [0] if components else []
    while pending:
        new = adjacency[pending.pop()] - reached
        reached.update(new)
        pending.extend(new)
    tree = (
        len(reached) == len(components)
        and maximum_intersection <= 1
        and len(links) == len(components) - 1
    )
    parent: list[int | None] = [None] * len(components)
    if tree:
        order = [0]
        seen = {0}
        for node in order:
            for child in sorted(adjacency[node] - seen):
                seen.add(child)
                parent[child] = node
                order.append(child)
    return {
        "component_count": len(components),
        "link_count": len(links),
        "maximum_star_intersection": maximum_intersection,
        "connected": len(reached) == len(components),
        "tree": tree,
        "parent": parent if tree else None,
    }


def _serialize_path(path: dict) -> dict:
    return {key: list(value) if isinstance(value, tuple) else value for key, value in path.items()}


def _serialize_endpoint(endpoint: tuple[str, int, int] | None) -> list | None:
    return None if endpoint is None else list(endpoint)


def build_report() -> dict:
    paths = local_paths()
    stable = []
    rejections = Counter()
    support_histogram = Counter()
    cap_cache: dict[tuple[int, frozenset[Vertex]], dict] = {}

    for path in paths:
        for endpoint in endpoint_states():
            records = []
            for k in (7, 8, 9):
                n = 3 * k + 2
                core, branch, exterior = materialize(k, path, endpoint)
                connector = connector_vertex(k, path, endpoint)
                if endpoint is not None and (connector is None or connector in exterior):
                    rejections["invalid_connector"] += 1
                    break
                if not branch:
                    rejections["empty_branch"] += 1
                    break
                if not unit_cells_valid(n, core):
                    rejections["unit_cell"] += 1
                    break
                if not forced_forest(n, core):
                    rejections["forced_cycle"] += 1
                    break
                articulation = articulation_data(n, branch, exterior)
                if k == 7:
                    support_histogram[articulation["intersection_size"]] += 1
                if not articulation["singleton"]:
                    rejections["not_singleton_articulation"] += 1
                    break
                cache_key = k, frozenset(core)
                if cache_key not in cap_cache:
                    cap_cache[cache_key] = cap_maximum(k, core)
                cap = cap_cache[cache_key]
                boundary = {tuple(vertex) for vertex in cap["witness"]}
                full = core | boundary
                incidence = incidence_parent_tree(n, full)
                records.append({
                    "k": k,
                    "core_count": len(core),
                    "branch_count": len(branch),
                    "bulk_correction": len(core) - 3 * k * k,
                    "articulation": articulation,
                    "cap_maximum": cap["maximum"],
                    "total": len(full),
                    "target": 3 * k * k + 7 * k,
                    "forced_forest": forced_forest(n, full),
                    "incidence": incidence,
                    "interface": {
                        "endpoint_state": _serialize_endpoint(endpoint),
                        "connector": list(connector) if connector is not None else None,
                        "cap_state_count_maximum": cap["state_count_maximum"],
                    },
                })
            if len(records) == 3:
                stable.append({
                    "path": _serialize_path(path),
                    "endpoint": _serialize_endpoint(endpoint),
                    "records": records,
                    "formulas": {
                        "branch": _quadratic_formula([(r["k"], r["branch_count"]) for r in records]),
                        "bulk_correction": _quadratic_formula([(r["k"], r["bulk_correction"]) for r in records]),
                        "cap": _quadratic_formula([(r["k"], r["cap_maximum"]) for r in records]),
                        "total": _quadratic_formula([(r["k"], r["total"]) for r in records]),
                    },
                })

    stable.sort(key=lambda item: tuple(record["total"] for record in item["records"]), reverse=True)
    target = [
        item for item in stable
        if all(record["total"] == record["target"] for record in item["records"])
    ]
    parent_trees = [
        item for item in stable
        if all(record["incidence"]["tree"] for record in item["records"])
    ]
    best = stable[0]
    best_interface_stable = (
        len({tuple(record["articulation"]["vertex"]) for record in best["records"]}) == 1
        and len({record["interface"]["cap_state_count_maximum"] for record in best["records"]}) == 1
        and all(record["interface"]["endpoint_state"] == best["endpoint"] for record in best["records"])
    )
    return {
        "schema": SCHEMA,
        "status": "family_found" if target else "buffered_branch_obstructed",
        "grammar": {
            "state": "(row mod 3, wall phase, shared advance, exterior phases, branch row/offset, endpoint state)",
            "outer_walls": "fixed separation three; shared advances in {0,1,2,3}; net advance three per packet",
            "branch": "one center at one of nine (packet row, buffer offset) phases per packet",
            "endpoint": "none, or one of 18 top/bottom packet connector states",
            "wall_packets": len(wall_packets()),
            "local_paths": len(paths),
            "endpoint_states": len(endpoint_states()),
            "width_cap": BUFFER_WIDTH,
        },
        "classification": {
            "stable_singleton_paths": len(stable),
            "stable_parent_tree_paths": len(parent_trees),
            "target_paths": len(target),
            "rejections": dict(sorted(rejections.items())),
            "k7_support_intersection_histogram": {
                str(size): count for size, count in sorted(support_histogram.items())
            },
        },
        "best_singleton_path": best,
        "stable_interface": {
            "best_path_stable": best_interface_stable,
            "endpoint_state": best["endpoint"],
            "articulation_vertex": best["records"][0]["articulation"]["vertex"],
            "cap_state_count": best["records"][0]["interface"]["cap_state_count_maximum"],
        },
        "obstruction": {
            "target": "3k^2+7k",
            "stable_gain_required": "6k+10",
            "best_total": best["formulas"]["total"],
            "best_successor_gains": [
                best["records"][1]["total"] - best["records"][0]["total"],
                best["records"][2]["total"] - best["records"][1]["total"],
            ],
            "complete_for": "fixed width-three blank buffer, one-site packet branch, and one finite endpoint connector",
        },
        "lower_gate": {
            "declared_finite_grammars_exhausted": True,
            "classes": [
                "affine interval families",
                "neighboring-residue extensions",
                "periodic density-one-third bulks",
                "one-wall staircase seams",
                "width-one/two elbow islands",
                "width-three buffered endpoint branches",
            ],
            "new_input_needed": "an unbounded or non-affine structural idea: branching incidence surgery with packet-dependent memory, a global dual-tree construction, or a theorem converting nonlocal connectivity into a uniform coordinate family",
        },
        "checks": {
            "ten_wall_packets": len(wall_packets()) == 10,
            "finite_endpoint_states": len(endpoint_states()) == 19,
            "stable_records_are_k_7_8_9": all(
                [record["k"] for record in item["records"]] == [7, 8, 9] for item in stable
            ),
            "all_stable_articulations_singleton": all(
                record["articulation"]["singleton"] for item in stable for record in item["records"]
            ),
            "all_stable_caps_forced_forests": all(
                record["forced_forest"] for item in stable for record in item["records"]
            ),
            "all_star_intersections_singleton": all(
                record["incidence"]["maximum_star_intersection"] <= 1
                for item in stable for record in item["records"]
            ),
            "best_interface_stable": best_interface_stable,
            "no_parent_tree_state": not parent_trees,
            "target_absent": not target,
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    rendered = json.dumps(build_report(), indent=2, sort_keys=True) + "\n"
    if args.check:
        if not args.output.exists() or args.output.read_text() != rendered:
            raise SystemExit(f"stale or missing artifact: {args.output}")
        print(f"buffered branch classification matches {args.output}")
    else:
        args.output.write_text(rendered)
        print(f"wrote {args.output}")


if __name__ == "__main__":
    main()
