#!/usr/bin/env python3
"""Finite checks for the straight-carrier contraction of a forced forest."""

from __future__ import annotations

import argparse
import json
from collections import deque
from dataclasses import asdict, dataclass

from analysis.bounds.forced_forest_row_grammar import is_forced_forest

Vertex = tuple[int, int]


@dataclass(frozen=True)
class CarrierRecord:
    vertices: tuple[Vertex, ...]
    axis: str
    length: int
    boundary_deficiency: int
    quotient_degree: int
    pendant_u_neighbors: int
    carriers_in_quotient_component: int


@dataclass(frozen=True)
class CarrierCheck:
    n: int
    forced_count: int
    carrier_count: int
    nonisolated_h_components: int
    isolated_u: int
    branching_u: int
    branching_excess: int
    boundary_deficiency_f: int
    boundary_deficiency_u: int
    row_carrier_occurrences: int
    column_carrier_occurrences: int
    target_margin: int
    naive_summation_margin: int
    carriers: tuple[CarrierRecord, ...]


def neighbors(n: int, vertex: Vertex):
    r, c = vertex
    for dr, dc in ((-1, 0), (1, 0), (0, -1), (0, 1)):
        rr, cc = r + dr, c + dc
        if 0 <= rr < n and 0 <= cc < n:
            yield rr, cc


def components(vertices: set[Vertex], adjacency) -> list[set[Vertex]]:
    unseen = set(vertices)
    result = []
    while unseen:
        root = unseen.pop()
        component = {root}
        queue = deque((root,))
        while queue:
            vertex = queue.popleft()
            for other in adjacency(vertex):
                if other in unseen:
                    unseen.remove(other)
                    component.add(other)
                    queue.append(other)
        result.append(component)
    return result


def check_carriers(n: int, rows: tuple[int, ...]) -> CarrierCheck:
    if n < 2 or len(rows) != n or not is_forced_forest(n, list(rows)):
        raise ValueError("rows must be a forced-acyclic square with n >= 2")

    all_vertices = {(r, c) for r in range(n) for c in range(n)}
    forced = {(r, c) for r in range(n) for c in range(n) if rows[r] >> c & 1}
    unforced = all_vertices - forced
    carrier_sets = components(forced, lambda v: (w for w in neighbors(n, v) if w in forced))
    carrier_of = {vertex: index for index, carrier in enumerate(carrier_sets) for vertex in carrier}
    u_degree = {
        vertex: sum(other in forced for other in neighbors(n, vertex))
        for vertex in unforced
    }

    quotient_adjacency: dict[tuple[str, object], set[tuple[str, object]]] = {
        ("C", index): set() for index in range(len(carrier_sets))
    }
    quotient_adjacency.update({("U", vertex): set() for vertex in unforced if u_degree[vertex]})
    for vertex in unforced:
        for other in neighbors(n, vertex):
            if other not in forced:
                continue
            left = ("U", vertex)
            right = ("C", carrier_of[other])
            # Parallel quotient attachments would already give a cycle in H.
            if right in quotient_adjacency[left]:
                raise AssertionError("one U vertex has two attachments to one carrier")
            quotient_adjacency[left].add(right)
            quotient_adjacency[right].add(left)

    quotient_edges = sum(map(len, quotient_adjacency.values())) // 2
    quotient_components = components(
        set(quotient_adjacency), lambda vertex: quotient_adjacency[vertex]
    )
    assert quotient_edges == len(quotient_adjacency) - len(quotient_components)
    quotient_component_of = {
        vertex: component
        for component in quotient_components
        for vertex in component
    }

    records = []
    row_occurrences = 0
    column_occurrences = 0
    for index, carrier in enumerate(carrier_sets):
        carrier_rows = {r for r, _c in carrier}
        carrier_columns = {c for _r, c in carrier}
        if len(carrier_rows) == 1:
            axis = "horizontal"
            ordered = sorted(carrier, key=lambda vertex: vertex[1])
            assert [c for _r, c in ordered] == list(range(ordered[0][1], ordered[-1][1] + 1))
        elif len(carrier_columns) == 1:
            axis = "vertical"
            ordered = sorted(carrier, key=lambda vertex: vertex[0])
            assert [r for r, _c in ordered] == list(range(ordered[0][0], ordered[-1][0] + 1))
        else:
            raise AssertionError("forced carrier is not straight")

        boundary = sum(4 - sum(1 for _ in neighbors(n, vertex)) for vertex in carrier)
        q_vertex = ("C", index)
        degree = len(quotient_adjacency[q_vertex])
        pendant = sum(
            len(quotient_adjacency[u_vertex]) == 1
            for u_vertex in quotient_adjacency[q_vertex]
        )
        quotient_component = quotient_component_of[q_vertex]
        carrier_total = sum(kind == "C" for kind, _value in quotient_component)
        length = len(carrier)
        assert degree == 2 * length + 2 - boundary
        assert degree - pendant <= carrier_total - 1
        row_occurrences += len(carrier_rows)
        column_occurrences += len(carrier_columns)
        records.append(
            CarrierRecord(
                tuple(ordered), axis, length, boundary, degree, pendant, carrier_total
            )
        )

    isolated_u = sum(degree == 0 for degree in u_degree.values())
    branching_u = sum(degree >= 2 for degree in u_degree.values())
    branching_excess = sum(max(0, degree - 1) for degree in u_degree.values())
    boundary_f = sum(record.boundary_deficiency for record in records)
    boundary_u = sum(
        4 - sum(1 for _ in neighbors(n, vertex)) for vertex in unforced
    )
    carrier_nonpendant_sum = sum(
        record.quotient_degree - record.pendant_u_neighbors for record in records
    )

    # These identities expose the exact one-unit congestion at every branching U.
    assert row_occurrences + column_occurrences == len(forced) + len(records)
    assert branching_excess == len(records) - len(quotient_components)
    assert carrier_nonpendant_sum == branching_excess + branching_u
    assert boundary_f + boundary_u == 4 * n

    return CarrierCheck(
        n=n,
        forced_count=len(forced),
        carrier_count=len(records),
        nonisolated_h_components=len(quotient_components),
        isolated_u=isolated_u,
        branching_u=branching_u,
        branching_excess=branching_excess,
        boundary_deficiency_f=boundary_f,
        boundary_deficiency_u=boundary_u,
        row_carrier_occurrences=row_occurrences,
        column_carrier_occurrences=column_occurrences,
        target_margin=boundary_u + len(records) + isolated_u + len(quotient_components) - (n + 4),
        naive_summation_margin=branching_excess - carrier_nonpendant_sum,
        carriers=tuple(records),
    )


def exhaustive_sets(n: int):
    row_mask = (1 << n) - 1
    for flat in range(1 << (n * n)):
        rows = tuple((flat >> (r * n)) & row_mask for r in range(n))
        if is_forced_forest(n, list(rows)):
            yield rows


def render(n: int, rows: tuple[int, ...]) -> list[str]:
    return ["".join("F" if rows[r] >> c & 1 else "U" for c in range(n)) for r in range(n)]


def report(brute_max_n: int) -> dict:
    exhaustive = []
    first_naive_counterexample = None
    for n in range(2, brute_max_n + 1):
        checked = 0
        target_violations = 0
        minimum_target_margin = None
        for rows in exhaustive_sets(n):
            result = check_carriers(n, rows)
            checked += 1
            target_violations += result.target_margin < 0
            minimum_target_margin = (
                result.target_margin
                if minimum_target_margin is None
                else min(minimum_target_margin, result.target_margin)
            )
            if result.naive_summation_margin < 0 and first_naive_counterexample is None:
                first_naive_counterexample = {
                    "rows": render(n, rows),
                    **asdict(result),
                }
        exhaustive.append(
            {
                "n": n,
                "forced_acyclic_sets": checked,
                "target_violations": target_violations,
                "minimum_target_margin": minimum_target_margin,
            }
        )
    return {
        "scope": "finite exhaustive validation only",
        "exhaustive": exhaustive,
        "first_counterexample_to_naive_global_branch_sum": first_naive_counterexample,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--brute-max-n", type=int, default=4)
    args = parser.parse_args()
    print(json.dumps(report(args.brute_max_n), indent=2))


if __name__ == "__main__":
    main()
