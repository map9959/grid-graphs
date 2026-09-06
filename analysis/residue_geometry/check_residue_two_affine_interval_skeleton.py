#!/usr/bin/env python3
"""Deterministically check the affine residue-two interval-star skeleton."""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from pathlib import Path
from typing import Iterable

from analysis.patterns.diagonal_patterns import residue_two_affine_pattern

Vertex = tuple[int, int]
Edge = tuple[Vertex, Vertex]
SCHEMA = "grid-graphs.residue-two-affine-rooted-interval-skeleton.v1"


def _neighbors(vertex: Vertex, n: int) -> Iterable[Vertex]:
    row, column = vertex
    if row:
        yield row - 1, column
    if row + 1 < n:
        yield row + 1, column
    if column:
        yield row, column - 1
    if column + 1 < n:
        yield row, column + 1


def _components(vertices: set[Vertex], n: int) -> list[frozenset[Vertex]]:
    remaining = set(vertices)
    result = []
    while remaining:
        seed = min(remaining)
        remaining.remove(seed)
        component = {seed}
        pending = [seed]
        while pending:
            vertex = pending.pop()
            for neighbor in _neighbors(vertex, n):
                if neighbor in remaining:
                    remaining.remove(neighbor)
                    component.add(neighbor)
                    pending.append(neighbor)
        result.append(frozenset(component))
    return result


def _is_straight_interval(component: frozenset[Vertex]) -> bool:
    rows = {row for row, _ in component}
    columns = {column for _, column in component}
    if len(rows) == 1:
        values = sorted(column for _, column in component)
    elif len(columns) == 1:
        values = sorted(row for row, _ in component)
    else:
        return False
    return values == list(range(values[0], values[-1] + 1))


def _forced_star(component: frozenset[Vertex], n: int) -> tuple[frozenset[Edge], frozenset[Vertex]]:
    edges: set[Edge] = set()
    for vertex in component:
        for neighbor in _neighbors(vertex, n):
            edges.add(tuple(sorted((vertex, neighbor))))
    support = frozenset(vertex for edge in edges for vertex in edge)
    return frozenset(edges), support


def _is_acyclic(edges: frozenset[Edge]) -> bool:
    parent: dict[Vertex, Vertex] = {}

    def find(vertex: Vertex) -> Vertex:
        parent.setdefault(vertex, vertex)
        while parent[vertex] != vertex:
            parent[vertex] = parent[parent[vertex]]
            vertex = parent[vertex]
        return vertex

    for left, right in sorted(edges):
        left_root, right_root = find(left), find(right)
        if left_root == right_root:
            return False
        parent[right_root] = left_root
    return True


def _leaf_elimination_order(supports: list[frozenset[Vertex]]) -> tuple[list[int], list[int]]:
    """Greedily remove the first star meeting its suffix at at most one vertex."""
    remaining = list(range(len(supports)))
    order: list[int] = []
    intersections: list[int] = []
    while remaining:
        selected = None
        for index in remaining:
            suffix_support = set().union(
                *(supports[other] for other in remaining if other != index)
            )
            size = len(supports[index] & suffix_support)
            if size <= 1:
                selected = (index, size)
                break
        if selected is None:
            return [], []
        index, size = selected
        remaining.remove(index)
        order.append(index)
        intersections.append(size)
    return order, intersections


def _connected(node_count: int, edges: list[dict]) -> bool:
    if node_count == 0:
        return True
    adjacency = [set() for _ in range(node_count)]
    for edge in edges:
        left, right = edge["stars"]
        adjacency[left].add(right)
        adjacency[right].add(left)
    reached = {0}
    pending = [0]
    while pending:
        new = adjacency[pending.pop()] - reached
        reached.update(new)
        pending.extend(sorted(new, reverse=True))
    return len(reached) == node_count


def _interval_key(component: frozenset[Vertex]) -> tuple[str, int, int, int]:
    rows = {row for row, _ in component}
    columns = {column for _, column in component}
    if len(rows) == 1:
        return "H", next(iter(rows)), min(columns), max(columns)
    if len(columns) == 1:
        return "V", next(iter(columns)), min(rows), max(rows)
    raise ValueError("component is not a straight interval")


def _interval_id(component: frozenset[Vertex]) -> str:
    orientation, fixed, start, end = _interval_key(component)
    fixed_axis, moving_axis = ("r", "c") if orientation == "H" else ("c", "r")
    return f"{orientation}:{fixed_axis}{fixed}:{moving_axis}{start}..{end}"


def _rooted_symbolic_skeleton(
    components: list[frozenset[Vertex]], n: int
) -> dict:
    """Name and canonically root a checked interval attachment tree."""
    components = sorted(components, key=_interval_key)
    supports = [_forced_star(component, n)[1] for component in components]
    adjacency: list[list[tuple[int, Vertex]]] = [[] for _ in components]
    for left in range(len(components)):
        for right in range(left + 1, len(components)):
            intersection = supports[left] & supports[right]
            if intersection:
                if len(intersection) != 1:
                    raise ValueError("rooted export requires singleton physical attachments")
                vertex = next(iter(intersection))
                adjacency[left].append((right, vertex))
                adjacency[right].append((left, vertex))

    root = 0
    parent: list[int | None] = [None] * len(components)
    attachment: list[Vertex | None] = [None] * len(components)
    order = [root]
    reached = {root}
    for node in order:
        for child, vertex in sorted(
            adjacency[node], key=lambda item: _interval_key(components[item[0]])
        ):
            if child in reached:
                continue
            reached.add(child)
            parent[child] = node
            attachment[child] = vertex
            order.append(child)
    if len(reached) != len(components):
        raise ValueError("rooted export requires a connected attachment graph")

    children: list[list[int]] = [[] for _ in components]
    for node, owner in enumerate(parent):
        if owner is not None:
            children[owner].append(node)
    nodes = []
    for index, component in enumerate(components):
        orientation, fixed, start, end = _interval_key(component)
        nodes.append({
            "id": _interval_id(component),
            "orientation": orientation,
            "fixed_coordinate": fixed,
            "endpoints": [start, end],
            "length": len(component),
            "parent": None if parent[index] is None else _interval_id(components[parent[index]]),
            "physical_parent_attachment": (
                None if attachment[index] is None else list(attachment[index])
            ),
            "children": [
                {
                    "id": _interval_id(components[child]),
                    "physical_attachment": list(attachment[child]),
                }
                for child in sorted(children[index], key=lambda item: _interval_key(components[item]))
            ],
        })
    return {
        "root_rule": "lexicographically least (orientation, fixed coordinate, start, end)",
        "root": _interval_id(components[root]),
        "nodes": nodes,
    }


def _insertion_occurrences(vertex: Vertex, n: int) -> set[Vertex]:
    """All successor occurrences under the duplicated affine row/column words."""
    row, column = vertex
    row_sources = [*range(9), 9, 10, 11, *range(9, n)]
    column_sources = [*range(4), 4, 5, 6, *range(4, n)]
    return {
        (new_row, new_column)
        for new_row, source_row in enumerate(row_sources) if source_row == row
        for new_column, source_column in enumerate(column_sources) if source_column == column
    }


def _standard_insertion_image(vertex: Vertex) -> Vertex:
    row, column = vertex
    return row + (3 if row >= 9 else 0), column + (3 if column >= 4 else 0)


def analyze_k(k: int) -> dict:
    """Return the complete deterministic interval-star check for one width."""
    if k < 5:
        raise ValueError("the affine residue-two family requires k >= 5")
    n = 3 * k + 2
    rows = residue_two_affine_pattern(n)
    preserved = {(row, column) for row, values in enumerate(rows)
                 for column, value in enumerate(values) if value == "."}
    components = _components(preserved, n)
    stars = [_forced_star(component, n) for component in components]
    supports = [support for _, support in stars]

    attachment_edges = []
    maximum_intersection = 0
    for left in range(len(stars)):
        for right in range(left + 1, len(stars)):
            intersection = sorted(supports[left] & supports[right])
            maximum_intersection = max(maximum_intersection, len(intersection))
            for vertex in intersection:
                attachment_edges.append({"stars": [left, right], "vertex": list(vertex)})

    order, suffix_intersections = _leaf_elimination_order(supports)
    star_acyclic = [_is_acyclic(edges) for edges, _ in stars]
    graph_connected = _connected(len(stars), attachment_edges)
    graph_tree = (
        graph_connected
        and maximum_intersection <= 1
        and len(attachment_edges) == len(stars) - 1
    )
    claims = {
        "component_count": {"expected": 4 * k, "observed": len(components)},
        "preserved_count": {
            "expected": 3 * k * k + 6 * k + 5,
            "observed": len(preserved),
        },
        "incidence_links": {"expected": 4 * k - 1, "observed": len(attachment_edges)},
        "attachment_connected": {"expected": True, "observed": graph_connected},
        "attachment_tree": {"expected": True, "observed": graph_tree},
    }
    for claim in claims.values():
        claim["status"] = "verified" if claim["observed"] == claim["expected"] else "claim_mismatch"

    checks = {
        "all_components_straight_intervals": all(map(_is_straight_interval, components)),
        "all_stars_acyclic": all(star_acyclic),
        "pairwise_active_support_intersection_at_most_one": maximum_intersection <= 1,
        "leaf_elimination_order_found": len(order) == len(stars),
        "leaf_elimination_suffix_intersection_at_most_one": (
            len(order) == len(stars) and max(suffix_intersections, default=0) <= 1
        ),
    }
    status = "verified" if all(checks.values()) and all(
        claim["status"] == "verified" for claim in claims.values()
    ) else "claim_mismatch"
    return {
        "k": k,
        "n": n,
        "status": status,
        "claims": claims,
        "checks": checks,
        "component_sizes": [len(component) for component in components],
        "star_edge_counts": [len(edges) for edges, _ in stars],
        "star_acyclic": star_acyclic,
        "maximum_pairwise_active_support_intersection": maximum_intersection,
        "physical_attachment_graph": {
            "node_count": len(stars),
            "link_count": len(attachment_edges),
            "links": attachment_edges,
            "connected": graph_connected,
            "tree": graph_tree,
        },
        "rooted_symbolic_skeleton": _rooted_symbolic_skeleton(components, n),
        "leaf_elimination_order": order,
        "leaf_elimination_suffix_intersection_sizes": suffix_intersections,
    }


def analyze_transition(k: int) -> dict:
    """Export the deterministic rooted-skeleton change from k to k+1."""
    source = analyze_k(k)
    target = analyze_k(k + 1)
    n, target_n = source["n"], target["n"]

    def interval_components(width: int) -> list[frozenset[Vertex]]:
        preserved = {
            (row, column)
            for row, values in enumerate(residue_two_affine_pattern(width))
            for column, value in enumerate(values) if value == "."
        }
        return sorted(_components(preserved, width), key=_interval_key)

    source_components = interval_components(n)
    target_components = interval_components(target_n)
    source_rooted = _rooted_symbolic_skeleton(source_components, n)
    target_rooted = _rooted_symbolic_skeleton(target_components, target_n)
    source_nodes = {node["id"]: node for node in source_rooted["nodes"]}
    target_nodes = {node["id"]: node for node in target_rooted["nodes"]}

    owners: list[int] = []
    ambiguities = []
    old_nodes = []
    for component in source_components:
        candidates = [
            index for index, successor in enumerate(target_components)
            if all(_insertion_occurrences(vertex, n) & successor for vertex in component)
        ]
        if not candidates:
            raise ValueError(f"no successor owner for {_interval_id(component)}")
        candidates.sort(key=lambda index: (
            -sum(
                _standard_insertion_image(vertex) in target_components[index]
                for vertex in component
            ),
            _interval_key(target_components[index]),
        ))
        owner = candidates[0]
        owners.append(owner)
        if len(candidates) > 1:
            ambiguities.append({
                "source": _interval_id(component),
                "candidates": [_interval_id(target_components[index]) for index in candidates],
                "chosen": _interval_id(target_components[owner]),
            })
        old_nodes.append({
            "source": _interval_id(component),
            "target": _interval_id(target_components[owner]),
            "source_length": len(component),
            "target_length": len(target_components[owner]),
            "length_gain": len(target_components[owner]) - len(component),
            "embedded_vertices": [
                list(min(_insertion_occurrences(vertex, n) & target_components[owner]))
                for vertex in sorted(component)
            ],
        })
    if len(set(owners)) != len(owners):
        raise ValueError("canonical old-node ownership is not injective")

    owner_by_source = {
        _interval_id(component): _interval_id(target_components[owner])
        for component, owner in zip(source_components, owners, strict=True)
    }
    old_parent_changes = []
    attachment_mismatches = []
    for source_id, target_id in owner_by_source.items():
        source_node, target_node = source_nodes[source_id], target_nodes[target_id]
        expected_parent = (
            None if source_node["parent"] is None
            else owner_by_source[source_node["parent"]]
        )
        if target_node["parent"] != expected_parent:
            old_parent_changes.append({
                "source": source_id,
                "old_parent_image": expected_parent,
                "new_parent": target_node["parent"],
            })
        old_attachment = source_node["physical_parent_attachment"]
        new_attachment = target_node["physical_parent_attachment"]
        if (
            old_attachment is not None
            and new_attachment is not None
            and tuple(new_attachment) not in _insertion_occurrences(tuple(old_attachment), n)
        ):
            attachment_mismatches.append({
                "source": source_id,
                "old_attachment": old_attachment,
                "new_attachment": new_attachment,
            })

    claimed = set(owners)
    new_nodes = [
        target_nodes[_interval_id(component)]
        for index, component in enumerate(target_components) if index not in claimed
    ]
    changed = [item for item in old_nodes if item["length_gain"]]
    observed_gain = sum(node["length"] for node in target_rooted["nodes"]) - sum(
        node["length"] for node in source_rooted["nodes"]
    )
    expected_new_ids = {
        "H:r2:c5..5",
        f"H:r12:c{3 * k - 1}..{3 * k - 1}",
        f"V:c6:r4..{3 * k + 2}",
        f"V:c{3 * k - 3}:r10..11",
    }
    checks = {
        "all_old_nodes_embedded_injectively": len(set(owners)) == 4 * k,
        "old_parent_map_transports": not old_parent_changes,
        "physical_parent_attachments_transport": not attachment_mismatches,
        "four_new_nodes_have_expected_formulas": {node["id"] for node in new_nodes} == expected_new_ids,
        "all_new_nodes_are_leaves": all(not node["children"] for node in new_nodes),
        "changed_node_count_is_k_plus_2": len(changed) == k + 2,
        "every_changed_length_gains_three": all(node["length_gain"] == 3 for node in changed),
        "new_node_length_sum_is_3k_plus_3": sum(node["length"] for node in new_nodes) == 3 * k + 3,
        "changed_length_sum_is_3k_plus_6": sum(node["length_gain"] for node in changed) == 3 * k + 6,
        "affine_gain_is_6k_plus_9": observed_gain == 6 * k + 9,
    }
    return {
        "k": k,
        "successor_k": k + 1,
        "status": "verified" if all(checks.values()) else "claim_mismatch",
        "insertion": {
            "rows": "0..8, 9,10,11, 9..n-1",
            "columns": "0..3, 4,5,6, 4..n-1",
            "standard_old_coordinate_map": "(r,c) -> (r+3*[r>=9], c+3*[c>=4])",
            "owner_tie_break": "maximize standard-image overlap, then interval order",
        },
        "source_root": source_rooted["root"],
        "target_root": target_rooted["root"],
        "old_nodes": old_nodes,
        "new_nodes": new_nodes,
        "changed_lengths": changed,
        "old_parent_changes": old_parent_changes,
        "physical_parent_attachment_mismatches": attachment_mismatches,
        "nonuniformity": {
            "raw_owner_relation_unique": not ambiguities,
            "ambiguous_old_node_count": len(ambiguities),
            "ambiguities": ambiguities,
            "note": "Duplicated source rows/columns give three old intervals two possible owners; the declared tie-break makes the export deterministic.",
        },
        "count_recurrence": {
            "old_node_count": 4 * k,
            "new_node_count": 4,
            "changed_node_count": len(changed),
            "new_node_length_gain": sum(node["length"] for node in new_nodes),
            "old_node_length_gain": sum(node["length_gain"] for node in changed),
            "total_gain": observed_gain,
            "required_target_gain": 6 * k + 10,
            "interface_mismatch": observed_gain - (6 * k + 10),
        },
        "exact_formulas": {
            "old_embedded_nodes": "4k (all source nodes)",
            "new_nodes": "4",
            "changed_old_nodes": "k+2",
            "changed_old_node_families": [
                "H:r0:c2..(3k+1) -> H:r0:c2..(3k+4)",
                "H:r(3k+1):c2..(3k-1) -> H:r(3k+4):c2..(3k+2)",
                "V:c0:r0..(3k+1) -> V:c0:r0..(3k+4)",
                "V:c3:r3..(3k-1) -> V:c3:r3..(3k+2)",
                "V:c(3j):r4..(3k-1) -> V:c(3j+3):r4..(3k+2), 2<=j<=k-3",
                "V:c(3k-2):r9..(3k-4) -> V:c(3k+1):r9..(3k-1)",
                "V:c(3k+1):r3..(3k+1) -> V:c(3k+4):r3..(3k+4)",
            ],
            "changed_old_length_gain": "3(k+2)=3k+6",
            "new_node_lengths": "1 + 1 + (3k-1) + 2 = 3k+3",
            "total_gain": "(3k+6)+(3k+3)=6k+9",
            "target_interface_deficit": "(6k+9)-(6k+10)=-1",
        },
        "checks": checks,
    }


def _polynomial_formula(points: list[tuple[int, int]]) -> str:
    """Interpolate the exact degree-at-most-two formula through three observations."""
    if len(points) != 3 or len({x for x, _ in points}) != 3:
        return "observations=" + repr(points)
    matrix = [[Fraction(x * x), Fraction(x), Fraction(1), Fraction(y)] for x, y in points]
    for column in range(3):
        pivot = next(row for row in range(column, 3) if matrix[row][column])
        matrix[column], matrix[pivot] = matrix[pivot], matrix[column]
        divisor = matrix[column][column]
        matrix[column] = [value / divisor for value in matrix[column]]
        for row in range(3):
            if row == column:
                continue
            factor = matrix[row][column]
            matrix[row] = [a - factor * b for a, b in zip(matrix[row], matrix[column])]
    coefficients = [matrix[row][3] for row in range(3)]

    def term(coefficient: Fraction, variable: str) -> str:
        magnitude = abs(coefficient)
        number = "" if magnitude == 1 and variable else str(magnitude)
        return number + variable

    rendered = ""
    for coefficient, variable in zip(coefficients, ("k^2", "k", "")):
        if not coefficient:
            continue
        piece = term(coefficient, variable)
        if not rendered:
            rendered = ("-" if coefficient < 0 else "") + piece
        else:
            rendered += (" - " if coefficient < 0 else " + ") + piece
    return rendered or "0"


def build_report(ks: tuple[int, ...] = (7, 8, 9)) -> dict:
    records = [analyze_k(k) for k in ks]
    transitions = [analyze_transition(k) for k in ks]
    formula_fields = ("component_count", "preserved_count", "incidence_links")
    formulas = {}
    for field in formula_fields:
        points = [(record["k"], record["claims"][field]["observed"]) for record in records]
        formulas[field] = {
            "observed_formula": _polynomial_formula(points),
            "observations": [{"k": k, "value": value} for k, value in points],
            "status": "verified" if all(
                record["claims"][field]["status"] == "verified" for record in records
            ) else "claim_mismatch",
        }
    return {
        "schema": SCHEMA,
        "checker": "residue_two_affine_interval_skeleton",
        "status": "verified" if all(record["status"] == "verified" for record in records)
                  and all(transition["status"] == "verified" for transition in transitions)
                  else "claim_mismatch",
        "k_values": list(ks),
        "observed_formulas": formulas,
        "records": records,
        "transitions": transitions,
        "scope": "deterministic symbolic audit at k=7,8,9; formulas are checked identities for the affine descriptors, not a target-skeleton claim",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="write JSON to this file instead of stdout")
    args = parser.parse_args()
    payload = json.dumps(build_report(), indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(payload)
    else:
        print(payload, end="")


if __name__ == "__main__":
    main()
