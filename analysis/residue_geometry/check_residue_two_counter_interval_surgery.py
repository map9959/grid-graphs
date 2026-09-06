#!/usr/bin/env python3
"""Check the abstract one-counter edge-subdivision surgery for lower L2."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from analysis.residue_geometry.check_residue_two_affine_interval_skeleton import (
    analyze_k,
    analyze_transition,
)

SCHEMA = "grid-graphs.residue-two-counter-interval-surgery.v1"
COUNTER_ID = "C:counter"


def _root_id(k: int) -> str:
    return f"H:r0:c2..{3 * k + 1}"


def _branch_id(k: int) -> str:
    return f"V:c0:r0..{3 * k + 1}"


def _leaf_order(parents: dict[str, str | None]) -> tuple[list[str], list[int]]:
    """Return a canonical postorder and its remaining-neighbor counts."""
    children = {node: [] for node in parents}
    root = next(node for node, parent in parents.items() if parent is None)
    for node, parent in parents.items():
        if parent is not None:
            children[parent].append(node)

    order: list[str] = []

    def visit(node: str) -> None:
        for child in sorted(children[node]):
            visit(child)
        order.append(node)

    visit(root)
    remaining = set(parents)
    intersections = []
    for node in order:
        neighbors = set(children[node])
        if parents[node] is not None:
            neighbors.add(parents[node])
        intersections.append(len(neighbors & (remaining - {node})))
        remaining.remove(node)
    return order, intersections


def analyze_surgery(k: int) -> dict:
    """Apply the abstract counter subdivision to the checked affine tree."""
    if k < 7:
        raise ValueError("the lower-L2 counter surgery is specified for k >= 7")
    affine = analyze_k(k)
    rooted = affine["rooted_symbolic_skeleton"]
    nodes = {node["id"]: node for node in rooted["nodes"]}
    root, branch = _root_id(k), _branch_id(k)
    if rooted["root"] != root or nodes[branch]["parent"] != root:
        raise ValueError("the stable affine root-to-c0 branch edge was not found")

    parents = {node_id: node["parent"] for node_id, node in nodes.items()}
    parents[branch] = COUNTER_ID
    parents[COUNTER_ID] = root

    # Existing affine attachment vertices are unique because their incidence
    # graph is a tree.  The removed (0,1) owner is replaced by two abstract L3
    # attachment obligations, not asserted grid coordinates.
    owners = {}
    for node_id, node in nodes.items():
        if node["parent"] is None or node_id == branch:
            continue
        owners[node_id] = f"affine:{tuple(node['physical_parent_attachment'])}"
    owners[COUNTER_ID] = "open:alpha_k(root,counter)"
    owners[branch] = "open:beta_k(counter,branch)"

    order, intersections = _leaf_order(parents)
    edge_count = sum(parent is not None for parent in parents.values())
    affine_length = sum(node["length"] for node in nodes.values())
    counter_length = k - 5
    total_length = affine_length + counter_length
    checks = {
        "stable_affine_edge_found": True,
        "one_root": sum(parent is None for parent in parents.values()) == 1,
        "parent_graph_has_node_minus_one_edges": edge_count == len(parents) - 1,
        "leaf_elimination_covers_all_nodes": len(order) == len(parents),
        "leaf_elimination_suffix_degree_at_most_one": max(intersections) <= 1,
        "symbolic_attachment_owners_are_unique": len(set(owners.values())) == len(owners),
        "counter_has_positive_length": counter_length >= 2,
        "target_cardinality": total_length == 3 * k * k + 7 * k,
    }
    return {
        "k": k,
        "status": "abstract_verified" if all(checks.values()) else "claim_mismatch",
        "affine_root": root,
        "detached_branch": branch,
        "deleted_attachment": {"parent": root, "child": branch, "owner": [0, 1]},
        "counter_interval": {
            "id": COUNTER_ID,
            "orientation": "H",
            "abstract_endpoints": ["0", "k-6"],
            "length": counter_length,
            "parent": root,
            "parent_attachment_owner": owners[COUNTER_ID],
            "child": branch,
            "child_attachment_owner": owners[branch],
            "grid_fixed_coordinate": None,
        },
        "parent_overrides": {
            COUNTER_ID: root,
            branch: COUNTER_ID,
        },
        "node_count": len(parents),
        "incidence_link_count": edge_count,
        "count": {
            "affine_length": affine_length,
            "counter_length": counter_length,
            "total_length": total_length,
            "target_formula": "(3k^2+6k+5)+(k-5)=3k^2+7k",
        },
        "leaf_elimination_order": order,
        "leaf_elimination_suffix_degrees": intersections,
        "checks": checks,
        "geometry": {
            "status": "open_L3",
            "obligations": [
                "realize C_k as a horizontal interval of length k-5",
                "remove the affine root-branch star intersection at (0,1)",
                "realize distinct singleton owners alpha_k and beta_k",
                "exclude all undeclared star intersections and unit-cell cycles",
            ],
        },
    }


def analyze_surgery_transition(k: int) -> dict:
    """Check that affine insertion transports the subdivided parent map."""
    source, target = analyze_surgery(k), analyze_surgery(k + 1)
    affine_transition = analyze_transition(k)
    owner_map = {
        node["source"]: node["target"] for node in affine_transition["old_nodes"]
    }
    owner_map[COUNTER_ID] = COUNTER_ID

    def parents(record: dict) -> dict[str, str | None]:
        affine_nodes = analyze_k(record["k"])["rooted_symbolic_skeleton"]["nodes"]
        result = {node["id"]: node["parent"] for node in affine_nodes}
        result.update(record["parent_overrides"])
        return result

    source_parents, target_parents = parents(source), parents(target)
    parent_mismatches = []
    for node, image in owner_map.items():
        parent = source_parents[node]
        expected = None if parent is None else owner_map[parent]
        if target_parents[image] != expected:
            parent_mismatches.append({
                "source": node,
                "target": image,
                "expected_parent": expected,
                "observed_parent": target_parents[image],
            })

    affine_recurrence = affine_transition["count_recurrence"]
    counter_gain = target["counter_interval"]["length"] - source["counter_interval"]["length"]
    total_gain = target["count"]["total_length"] - source["count"]["total_length"]
    checks = {
        "all_old_nodes_have_images": len(owner_map) == 4 * k + 1,
        "uniform_parent_map_transports": not parent_mismatches,
        "counter_endpoint_moves_by_one": counter_gain == 1,
        "affine_gain_is_6k_plus_9": affine_recurrence["total_gain"] == 6 * k + 9,
        "surgery_gain_is_6k_plus_10": total_gain == 6 * k + 10,
        "four_affine_new_nodes_remain_leaves": all(
            not node["children"] for node in affine_transition["new_nodes"]
        ),
        "successor_leaf_elimination": all(target["checks"].values()),
    }
    return {
        "k": k,
        "successor_k": k + 1,
        "status": "abstract_verified" if all(checks.values()) else "claim_mismatch",
        "insertion_map": {
            "affine_nodes": "the checked affine owner map",
            "counter": "C_k -> C_(k+1)",
            "counter_local_coordinate": "i -> i for 0<=i<=k-6",
            "counter_new_endpoint": "k-5",
        },
        "parent_mismatches": parent_mismatches,
        "new_affine_leaves": [node["id"] for node in affine_transition["new_nodes"]],
        "gain": {
            "changed_affine_old_intervals": "k+2, each gaining 3",
            "changed_affine_old_length": 3 * k + 6,
            "new_affine_interval_length": 3 * k + 3,
            "counter_length_change": counter_gain,
            "total": total_gain,
            "formula": "(3k+6)+(3k+3)+1=6k+10",
        },
        "checks": checks,
    }


def build_report(ks: tuple[int, ...] = (7, 8, 9)) -> dict:
    records = [analyze_surgery(k) for k in ks]
    transitions = [analyze_surgery_transition(k) for k in ks]
    verified = all(record["status"] == "abstract_verified" for record in records)
    verified &= all(item["status"] == "abstract_verified" for item in transitions)
    return {
        "schema": SCHEMA,
        "checker": "residue_two_counter_interval_surgery",
        "status": "abstract_verified_geometry_open" if verified else "claim_mismatch",
        "k_values": list(ks),
        "symbolic_claim": {
            "range": "k>=7",
            "index_type": "AffineNode(k) + {C_k}",
            "deleted_parent_edge": "R_k -> B_k",
            "replacement_parent_path": "R_k -> C_k -> B_k",
            "counter_length": "k-5",
            "total_length": "3k^2+7k",
            "step_gain": "6k+10",
        },
        "records": records,
        "transitions": transitions,
        "scope": (
            "Exact abstract parent/count identities for arbitrary k>=7, with deterministic "
            "audits at listed widths; alpha_k and beta_k remain explicit L3 grid obligations."
        ),
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
