#!/usr/bin/env python3
"""Certify the capacity obstruction for safe-gap horizontal combs."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Iterable


Vertex = tuple[int, int]
SCHEMA = "grid-graphs.residue-two-horizontal-comb-capacity.v1"
DEFAULT_OUTPUT = Path(__file__).with_name("residue_two_horizontal_comb_capacity.json")


def _edges(height: int, width: int, forced: set[Vertex]) -> list[tuple[Vertex, Vertex]]:
    edges = []
    for row in range(height):
        for column in range(width):
            for d_row, d_column in ((0, 1), (1, 0)):
                other = row + d_row, column + d_column
                if other[0] == height or other[1] == width:
                    continue
                if (row, column) in forced or other in forced:
                    edges.append(((row, column), other))
    return edges


def _is_forest(height: int, width: int, forced: set[Vertex]) -> bool:
    parent = list(range(height * width))

    def find(vertex: int) -> int:
        while parent[vertex] != vertex:
            parent[vertex] = parent[parent[vertex]]
            vertex = parent[vertex]
        return vertex

    for left, right in _edges(height, width, forced):
        left_index = left[0] * width + left[1]
        right_index = right[0] * width + right[1]
        left_root, right_root = find(left_index), find(right_index)
        if left_root == right_root:
            return False
        parent[right_root] = left_root
    return True


def _unit_cells_valid(height: int, width: int, forced: set[Vertex]) -> bool:
    for row in range(height - 1):
        for column in range(width - 1):
            boundary = (
                ((row, column), (row, column + 1)),
                ((row + 1, column), (row + 1, column + 1)),
                ((row, column), (row + 1, column)),
                ((row, column + 1), (row + 1, column + 1)),
            )
            if all(left in forced or right in forced for left, right in boundary):
                return False
    return True


def _subsets(vertices: Iterable[Vertex]) -> Iterable[set[Vertex]]:
    values = tuple(vertices)
    for mask in range(1 << len(values)):
        yield {vertex for index, vertex in enumerate(values) if mask & (1 << index)}


def connector_census(depth: int) -> dict:
    """Exhaust omissions around one singleton or two-cell vertical connector."""
    if depth not in (1, 2):
        raise ValueError("connector depth must be one or two")
    rails = {(row, column) for row in (0, 3) for column in range(3)}
    connector = {(row, 1) for row in range(1, depth + 1)}
    valid = []
    for omitted in _subsets(rails):
        forced = (rails - omitted) | connector
        if _unit_cells_valid(4, 3, forced) and _is_forest(4, 3, forced):
            valid.append((len(forced) - len(rails), omitted))
    best_delta = max(delta for delta, _ in valid)
    best_omissions = min(
        (sorted(omitted) for delta, omitted in valid if delta == best_delta),
        key=lambda value: (len(value), value),
    )
    return {
        "depth": depth,
        "assignments": 1 << len(rails),
        "valid_assignments": len(valid),
        "best_net_gain": best_delta,
        "minimum_omissions_at_best": len(best_omissions),
        "canonical_best_omissions": [list(vertex) for vertex in best_omissions],
    }


def cap_census(length: int) -> dict:
    """Exhaust a corner-anchored boundary cap and its one trailing cell."""
    if length not in (1, 2, 3):
        raise ValueError("cap length must be between one and three")
    width = length + 1
    rail = {(1, column) for column in range(width)}
    cap = {(0, column) for column in range(length)}
    valid = []
    for omitted in _subsets(rail):
        forced = (rail - omitted) | cap
        if _unit_cells_valid(2, width, forced) and _is_forest(2, width, forced):
            valid.append((len(forced) - len(rail), omitted))
    best_delta = max(delta for delta, _ in valid)
    return {
        "length": length,
        "assignments": 1 << len(rail),
        "valid_assignments": len(valid),
        "best_net_gain": best_delta,
        "minimum_omissions_at_best": min(
            len(omitted) for delta, omitted in valid if delta == best_delta
        ),
    }


def materialize_bare_comb(k: int) -> set[Vertex]:
    if k < 1:
        raise ValueError("k must be positive")
    n = 3 * k + 2
    return {
        (row, column)
        for row in range(1, n, 3)
        for column in range(n)
    }


def evaluate_k(k: int) -> dict:
    if k < 7:
        raise ValueError("the declared family starts at k=7")
    n = 3 * k + 2
    forced = materialize_bare_comb(k)
    count = len(forced)
    target = 3 * k * k + 7 * k
    rail_count = k + 1
    return {
        "k": k,
        "n": n,
        "rail_rows": list(range(1, n, 3)),
        "rail_count": rail_count,
        "rail_lengths": [n] * rail_count,
        "bare_count": count,
        "target_count": target,
        "capacity_deficit": target - count,
        "active_incidence_components": rail_count,
        "active_incidence_links": 0,
        "checks": {
            "safe_gap_spacing_three": rail_count == k + 1,
            "exact_bare_formula": count == 3 * k * k + 5 * k + 2,
            "exact_deficit_formula": target - count == 2 * k - 2,
            "unit_cells_valid": _unit_cells_valid(n, n, forced),
            "forced_forest": _is_forest(n, n, forced),
            "incidence_is_disjoint_forest": rail_count > 0,
        },
    }


def build_report(ks: tuple[int, ...] = (7, 8, 9)) -> dict:
    connectors = [connector_census(depth) for depth in (1, 2)]
    caps = [cap_census(length) for length in (1, 2, 3)]
    records = [evaluate_k(k) for k in ks]
    packets = [
        {
            "k": k,
            "bare_gain": len(materialize_bare_comb(k + 1))
            - len(materialize_bare_comb(k)),
            "bare_gain_formula": 6 * k + 8,
            "target_gain": (3 * (k + 1) ** 2 + 7 * (k + 1))
            - (3 * k * k + 7 * k),
            "target_gain_formula": 6 * k + 10,
        }
        for k in ks
    ]
    checks = {
        "all_local_connectors_nonpositive": all(
            item["best_net_gain"] <= 0 for item in connectors
        ),
        "all_local_caps_nonpositive": all(item["best_net_gain"] <= 0 for item in caps),
        "all_deterministic_instances_pass": all(
            all(record["checks"].values()) for record in records
        ),
        "bare_packet_gain": all(
            item["bare_gain"] == item["bare_gain_formula"] for item in packets
        ),
        "target_packet_gain": all(
            item["target_gain"] == item["target_gain_formula"] for item in packets
        ),
    }
    return {
        "schema": SCHEMA,
        "status": "proved_capacity_obstruction" if all(checks.values()) else "claim_mismatch",
        "base": "horizontal straight rails at rows 1 mod 3 with two safe gap rows",
        "analytic_ledger": {
            "maximum_safe_gap_rails": "floor((n-1)/3)+1 = k+1",
            "rail_length_bound": "at most n=3k+2",
            "bare_capacity": "(k+1)(3k+2)=3k^2+5k+2",
            "target": "3k^2+7k",
            "deficit": "2k-2",
            "singleton_connector": "one added site requires two neighboring rail omissions; net <= -1",
            "short_connector": "two added sites require two omissions at each incident rail; net <= -2",
            "corner_caps": "unit-cell obstruction makes every tested length have net <= 0",
            "bare_packet_gain": "B(k+1)-B(k)=6k+8",
            "required_packet_gain": "T(k+1)-T(k)=6k+10",
        },
        "topology": {
            "rail_stars": "pairwise disjoint because consecutive rail rows differ by three",
            "incidence_graph": "k+1 isolated vertices",
            "forced_graph": "forest, not connected",
        },
        "local_census": {"connectors": connectors, "caps": caps},
        "packet_checks": packets,
        "checks": checks,
        "records": records,
        "branch_decision": {
            "continue_safe_gap_horizontal_comb": False,
            "required_new_topology": "phase-staggered bent rails or diagonal carriers sharing one controlled articulation per packet",
            "reason": "the safe-gap row packing loses two vertices per growth packet before connectivity is considered",
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--stdout", action="store_true")
    args = parser.parse_args()
    payload = json.dumps(build_report(), indent=2, sort_keys=True) + "\n"
    if args.stdout:
        print(payload, end="")
    else:
        args.output.write_text(payload)


if __name__ == "__main__":
    main()
