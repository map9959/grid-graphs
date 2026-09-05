#!/usr/bin/env python3
"""Canonical insertion-circuit routing and finite congestion census.

For an inclusion-maximal forced forest H(F), inserting u in U adds precisely
the U-U grid edges incident with u.  At least one circuit is created.  This
tool enumerates all such circuits, compares explicit selection quantifiers, and
uses (edge count, sorted edge list) for the promoted canonical selection.

All reported conclusions are finite computational evidence, not proof claims.
"""

from __future__ import annotations

import argparse
import json
import random
from collections import Counter, deque
from dataclasses import dataclass
from itertools import combinations
from typing import Iterable

from bundle_cycle_defect_census import (
    adversarial_maximal_witnesses,
    defect_profile,
    maximalize,
    maximal_profiles,
    neighbors,
    render_rows,
)


Edge = tuple[int, int]
BoundaryUnit = tuple[str, int]


def edge(left: int, right: int) -> Edge:
    return (left, right) if left < right else (right, left)


def _path(
    adjacency: tuple[tuple[int, ...], ...],
    start: int,
    finish: int,
    forbidden: int | None,
) -> tuple[int, ...] | None:
    """Return the unique forest path, optionally deleting one vertex."""
    if start == forbidden or finish == forbidden:
        return None
    parent = {start: -1}
    queue = deque([start])
    while queue:
        vertex = queue.popleft()
        if vertex == finish:
            result = []
            while vertex != -1:
                result.append(vertex)
                vertex = parent[vertex]
            return tuple(reversed(result))
        for other in adjacency[vertex]:
            if other != forbidden and other not in parent:
                parent[other] = vertex
                queue.append(other)
    return None


def _turns(n: int, vertices: tuple[int, ...]) -> int:
    points = [divmod(vertex, n) for vertex in vertices[:-1]]
    count = 0
    for index, current in enumerate(points):
        previous = points[index - 1]
        following = points[(index + 1) % len(points)]
        incoming = (current[0] - previous[0], current[1] - previous[1])
        outgoing = (following[0] - current[0], following[1] - current[1])
        count += incoming != outgoing
    return count


def _enclosed_cells(n: int, vertices: tuple[int, ...]) -> tuple[int, ...]:
    """Return row-major unit cells whose centers are inside the grid polygon."""
    polygon = [divmod(vertex, n) for vertex in vertices[:-1]]
    enclosed = []
    for row in range(n - 1):
        for column in range(n - 1):
            # Horizontal ray from (row+1/2,column+1/2), using doubled values.
            y2, x2 = 2 * row + 1, 2 * column + 1
            inside = False
            for index, (r1, c1) in enumerate(polygon):
                r2, c2 = polygon[(index + 1) % len(polygon)]
                if c1 != c2:  # Horizontal polygon edges never cross the ray.
                    continue
                edge_x2 = 2 * c1
                low_y2, high_y2 = sorted((2 * r1, 2 * r2))
                if low_y2 < y2 < high_y2 and edge_x2 > x2:
                    inside = not inside
            if inside:
                enclosed.append(row * (n - 1) + column)
    return tuple(enclosed)


def _boundary_units(n: int, edges: Iterable[Edge]) -> tuple[BoundaryUnit, ...]:
    result = []
    for left, right in edges:
        lr, lc = divmod(left, n)
        rr, rc = divmod(right, n)
        if lr == rr == 0:
            result.append(("top", min(lc, rc)))
        if lr == rr == n - 1:
            result.append(("bottom", min(lc, rc)))
        if lc == rc == 0:
            result.append(("left", min(lr, rr)))
        if lc == rc == n - 1:
            result.append(("right", min(lr, rr)))
    return tuple(sorted(result))


def _u_component_labels(n: int, unforced: set[int]) -> dict[int, int]:
    labels: dict[int, int] = {}
    for root in sorted(unforced):
        if root in labels:
            continue
        labels[root] = root
        queue = [root]
        while queue:
            vertex = queue.pop()
            for other in neighbors(n, vertex):
                if other in unforced and other not in labels:
                    labels[other] = root
                    queue.append(other)
    return labels


@dataclass(frozen=True)
class InsertionCircuit:
    owner: int
    vertices: tuple[int, ...]
    edges: tuple[Edge, ...]
    inserted_edges: tuple[Edge, ...]
    h_edges: tuple[Edge, ...]
    enclosed_cells: tuple[int, ...]
    rows: tuple[int, ...]
    boundary_units: tuple[BoundaryUnit, ...]
    u_components: tuple[int, ...]
    turns: int

    @property
    def length(self) -> int:
        return len(self.edges)


def canonical_insertion_circuits(
    n: int, rows: Iterable[int]
) -> tuple[InsertionCircuit, ...]:
    """Choose one shortest, then edge-lexicographic, circuit for every u in U."""
    return select_insertion_circuits(n, rows, "shortest_lex")


def insertion_circuit_options(
    n: int, rows: Iterable[int]
) -> tuple[tuple[InsertionCircuit, ...], ...]:
    """Enumerate every distinct simple insertion circuit, grouped by owner."""
    rows = tuple(rows)
    profile = defect_profile(n, rows)
    if not profile.maximal:
        raise ValueError("rows must encode an inclusion-maximal forced forest")
    forced = {
        row * n + column
        for row, mask in enumerate(rows)
        for column in range(n)
        if mask >> column & 1
    }
    unforced = set(range(n * n)) - forced
    h_adjacency = tuple(
        tuple(other for other in neighbors(n, vertex) if vertex in forced or other in forced)
        for vertex in range(n * n)
    )
    component = _u_component_labels(n, unforced)
    result = []
    for owner in sorted(unforced):
        leaves = sorted(other for other in neighbors(n, owner) if other in unforced)
        candidates: list[
            tuple[tuple[int, tuple[Edge, ...]], tuple[int, ...], tuple[Edge, ...]]
        ] = []

        for leaf in leaves:
            path = _path(h_adjacency, leaf, owner, forbidden=None)
            if path is not None:
                vertices = (owner,) + path
                edges = tuple(
                    sorted(
                        edge(vertices[i], vertices[i + 1])
                        for i in range(len(vertices) - 1)
                    )
                )
                candidates.append(((len(edges), edges), vertices, (edge(owner, leaf),)))

        for left, right in combinations(leaves, 2):
            path = _path(h_adjacency, left, right, forbidden=owner)
            if path is not None:
                vertices = (owner,) + path + (owner,)
                edges = tuple(sorted(edge(vertices[i], vertices[i + 1]) for i in range(len(vertices) - 1)))
                inserted = tuple(sorted((edge(owner, left), edge(owner, right))))
                candidates.append(((len(edges), edges), vertices, inserted))

        if not candidates:
            raise AssertionError("maximality did not produce an insertion circuit")
        owner_options = []
        seen_edges = set()
        for _key, vertices, inserted in sorted(candidates, key=lambda item: item[0]):
            cycle_edges = tuple(
                sorted(
                    edge(vertices[i], vertices[i + 1])
                    for i in range(len(vertices) - 1)
                )
            )
            if cycle_edges in seen_edges:
                continue
            seen_edges.add(cycle_edges)
            if (
                len(set(vertices[:-1])) != len(vertices) - 1
                or len(set(cycle_edges)) != len(cycle_edges)
            ):
                raise AssertionError("insertion circuit is not simple")
            h_edges = tuple(item for item in cycle_edges if item not in inserted)
            cycle_u = {vertex for vertex in vertices[:-1] if vertex in unforced}
            owner_options.append(
                InsertionCircuit(
                    owner=owner,
                    vertices=vertices,
                    edges=cycle_edges,
                    inserted_edges=inserted,
                    h_edges=h_edges,
                    enclosed_cells=_enclosed_cells(n, vertices),
                    rows=tuple(sorted({vertex // n for vertex in vertices[:-1]})),
                    boundary_units=_boundary_units(n, cycle_edges),
                    u_components=tuple(sorted({component[vertex] for vertex in cycle_u})),
                    turns=_turns(n, vertices),
                )
            )
        result.append(tuple(owner_options))
    return tuple(result)


def select_insertion_circuits(
    n: int, rows: Iterable[int], choice: str
) -> tuple[InsertionCircuit, ...]:
    """Select one circuit per owner under an explicit deterministic policy."""
    options = insertion_circuit_options(n, rows)
    return _select_options(options, choice)


def _select_options(
    options: tuple[tuple[InsertionCircuit, ...], ...], choice: str
) -> tuple[InsertionCircuit, ...]:
    if choice == "shortest_lex":
        key = lambda circuit: (circuit.length, circuit.edges)
    elif choice == "minimum_turns":
        key = lambda circuit: (circuit.turns, circuit.length, circuit.edges)
    elif choice == "maximum_turns":
        key = lambda circuit: (-circuit.turns, circuit.length, circuit.edges)
    else:
        raise ValueError(f"unknown circuit choice: {choice}")
    return tuple(min(owner_options, key=key) for owner_options in options)


def turning_inequality_margin(
    n: int, rows: Iterable[int], choice: str = "shortest_lex"
) -> int:
    """Return the direct TURN margin for a one-per-owner selection policy."""
    rows = tuple(rows)
    base = defect_profile(n, rows)
    if choice not in {"shortest_lex", "minimum_turns", "maximum_turns"}:
        raise ValueError(f"unknown circuit choice: {choice}")
    forced = {
        row * n + column
        for row, mask in enumerate(rows)
        for column in range(n)
        if mask >> column & 1
    }
    unforced = set(range(n * n)) - forced
    h_adjacency = tuple(
        tuple(other for other in neighbors(n, vertex) if vertex in forced or other in forced)
        for vertex in range(n * n)
    )
    turns = 0
    for owner in sorted(unforced):
        leaves = sorted(other for other in neighbors(n, owner) if other in unforced)
        candidates = []
        for leaf in leaves:
            path = _path(h_adjacency, leaf, owner, forbidden=None)
            if path is not None:
                vertices = (owner,) + path
                cycle_edges = tuple(
                    sorted(edge(vertices[i], vertices[i + 1]) for i in range(len(vertices) - 1))
                )
                candidates.append((len(cycle_edges), cycle_edges, _turns(n, vertices)))
        for left, right in combinations(leaves, 2):
            path = _path(h_adjacency, left, right, forbidden=owner)
            if path is not None:
                vertices = (owner,) + path + (owner,)
                cycle_edges = tuple(
                    sorted(edge(vertices[i], vertices[i + 1]) for i in range(len(vertices) - 1))
                )
                candidates.append((len(cycle_edges), cycle_edges, _turns(n, vertices)))
        if choice == "shortest_lex":
            selected = min(candidates, key=lambda item: item[:2])
        elif choice == "minimum_turns":
            selected = min(candidates, key=lambda item: (item[2], item[0], item[1]))
        else:
            selected = min(candidates, key=lambda item: (-item[2], item[0], item[1]))
        turns += selected[2]
    return (
        5 * n * n + 3 * n - 3 - 7 * base.forced
        - base.unforced_induced_components - turns
    )


def _loads(circuits: Iterable[InsertionCircuit], attribute: str) -> Counter:
    loads: Counter = Counter()
    for circuit in circuits:
        loads.update(getattr(circuit, attribute))
    return loads


def _load_summary(loads: Counter) -> dict:
    return {
        "resources_used": len(loads),
        "total_use": sum(loads.values()),
        "maximum_load": max(loads.values(), default=0),
        "load_distribution": dict(sorted(Counter(loads.values()).items())),
    }


def congestion_profile(n: int, rows: Iterable[int]) -> dict:
    rows = tuple(rows)
    base = defect_profile(n, rows)
    options = insertion_circuit_options(n, rows)
    circuits = _select_options(options, "shortest_lex")
    resources = {
        name: _load_summary(_loads(circuits, attribute))
        for name, attribute in (
            ("H_edges", "h_edges"),
            ("U_U_edges", "inserted_edges"),
            ("cells", "enclosed_cells"),
            ("rows", "rows"),
            ("boundary_units", "boundary_units"),
            ("U_components", "u_components"),
        )
    }
    total_length = sum(circuit.length for circuit in circuits)
    path_excess = total_length - 4 * base.unforced
    if path_excess < 0:
        raise AssertionError("a simple grid circuit has at least four edges")
    total_turns = sum(circuit.turns for circuit in circuits)
    turn_excess = total_turns - 4 * base.unforced
    if turn_excess < 0:
        raise AssertionError(
            "a simple rectilinear circuit has at least four turns"
        )
    choice_totals = {
        choice: sum(circuit.turns for circuit in _select_options(options, choice))
        for choice in ("shortest_lex", "minimum_turns", "maximum_turns")
    }
    choice_totals["all_circuits"] = sum(
        circuit.turns for owner_options in options for circuit in owner_options
    )
    choice_margins = {
        choice: 5 * n * n + 3 * n - 3 - 7 * base.forced
        - base.unforced_induced_components - turns
        for choice, turns in choice_totals.items()
    }
    return {
        "n": n,
        "rows": render_rows(rows),
        "forced": base.forced,
        "unforced": base.unforced,
        "u_components": base.unforced_induced_components,
        "target_margin": base.target_margin,
        "strengthened_margin": base.component_strengthened_margin,
        "total_length": total_length,
        "path_excess": path_excess,
        "total_turns": total_turns,
        "turn_excess": turn_excess,
        "turning_inequality_margin": base.component_strengthened_margin - turn_excess,
        "circuit_option_distribution": dict(
            sorted(Counter(len(owner_options) for owner_options in options).items())
        ),
        "turn_totals_by_quantifier": choice_totals,
        "turning_margins_by_quantifier": choice_margins,
        "length_distribution": dict(
            sorted(Counter(circuit.length for circuit in circuits).items())
        ),
        "turn_distribution": dict(
            sorted(Counter(circuit.turns for circuit in circuits).items())
        ),
        "one_edge_insertions": sum(
            len(circuit.inserted_edges) == 1 for circuit in circuits
        ),
        "two_edge_insertions": sum(
            len(circuit.inserted_edges) == 2 for circuit in circuits
        ),
        "resources": resources,
    }


def _summary(n: int, coverage: str, samples: list[tuple[int, ...]]) -> dict:
    profiles = [congestion_profile(n, rows) for rows in samples]
    minimum_turning_margin = min(
        item["turning_inequality_margin"] for item in profiles
    )

    def required_multiplier(excess_name: str) -> int | None:
        required = 0
        for item in profiles:
            excess = item[excess_name]
            slack = item["strengthened_margin"]
            if excess and slack <= 0:
                return None
            if excess:
                required = max(required, (excess + slack - 1) // slack)
        return required

    return {
        "n": n,
        "coverage": coverage,
        "checked": len(profiles),
        "minimum_strengthened_margin": min(item["strengthened_margin"] for item in profiles),
        "minimum_turning_inequality_margin": minimum_turning_margin,
        "turning_inequality_equalities": sum(
            item["turning_inequality_margin"] == 0 for item in profiles
        ),
        "turning_quantifiers": {
            choice: {
                "minimum_margin": min(
                    item["turning_margins_by_quantifier"][choice] for item in profiles
                ),
                "equalities": sum(
                    item["turning_margins_by_quantifier"][choice] == 0
                    for item in profiles
                ),
                "failures": sum(
                    item["turning_margins_by_quantifier"][choice] < 0
                    for item in profiles
                ),
                "margin_distribution": {
                    str(margin): count
                    for margin, count in sorted(
                        Counter(
                            item["turning_margins_by_quantifier"][choice]
                            for item in profiles
                        ).items()
                    )
                },
                "first_minimum_witness": next(
                    {
                        "rows": item["rows"],
                        "turns": item["turn_totals_by_quantifier"][choice],
                    }
                    for item in profiles
                    if item["turning_margins_by_quantifier"][choice]
                    == min(
                        profile["turning_margins_by_quantifier"][choice]
                        for profile in profiles
                    )
                ),
            }
            for choice in (
                "shortest_lex", "minimum_turns", "maximum_turns", "all_circuits"
            )
        },
        "shortest_lex_vs_minimum_turn_disagreements": sum(
            item["turn_totals_by_quantifier"]["shortest_lex"]
            != item["turn_totals_by_quantifier"]["minimum_turns"]
            for item in profiles
        ),
        "required_slack_multipliers": {
            "path_excess": required_multiplier("path_excess"),
            "turn_excess": required_multiplier("turn_excess"),
        },
        "maxima": {
            "circuit_length": max(
                max(map(int, item["length_distribution"]), default=0)
                for item in profiles
            ),
            "H_edge_load": max(item["resources"]["H_edges"]["maximum_load"] for item in profiles),
            "U_U_edge_load": max(item["resources"]["U_U_edges"]["maximum_load"] for item in profiles),
            "cell_load": max(item["resources"]["cells"]["maximum_load"] for item in profiles),
            "row_load": max(item["resources"]["rows"]["maximum_load"] for item in profiles),
            "boundary_unit_load": max(item["resources"]["boundary_units"]["maximum_load"] for item in profiles),
            "U_component_load": max(item["resources"]["U_components"]["maximum_load"] for item in profiles),
        },
        "first_minimum_witness": next(
            item
            for item in profiles
            if item["strengthened_margin"]
            == min(p["strengthened_margin"] for p in profiles)
        ),
        "first_minimum_turning_witness": next(
            item
            for item in profiles
            if item["turning_inequality_margin"] == minimum_turning_margin
        ),
    }


def adversarial_turning_witnesses(
    n: int, attempts: int, seed: int, choice: str = "shortest_lex"
) -> list[tuple[int, ...]]:
    """Mutate maximal sets to minimize the chosen turning-inequality margin."""
    if choice not in {"shortest_lex", "minimum_turns", "maximum_turns"}:
        raise ValueError("mutation requires a one-circuit-per-owner policy")
    rng = random.Random(seed)
    vertices = list(range(n * n))
    seeds = adversarial_maximal_witnesses(n, attempts, seed)
    retained = {rows for rows, _profile in seeds}
    if n == 9:
        # Exact per-owner minimization still violates TURN on this maximal set.
        retained.add((255, 0, 292, 293, 289, 297, 257, 256, 383))

    def score(rows: tuple[int, ...]) -> int:
        return turning_inequality_margin(n, rows, choice)

    current = min(retained, key=score)
    current_score = score(current)
    for attempt in range(attempts):
        if attempt % max(1, attempts // 8) == 0:
            shuffled = vertices.copy()
            rng.shuffle(shuffled)
            candidate = maximalize(n, (0,) * n, shuffled)
        else:
            forced = [
                vertex for vertex in vertices
                if current[vertex // n] >> (vertex % n) & 1
            ]
            candidate_rows = list(current)
            remove_count = min(len(forced), rng.choice((1, 1, 2, 3, 4)))
            for vertex in rng.sample(forced, remove_count):
                candidate_rows[vertex // n] &= ~(1 << (vertex % n))
            shuffled = vertices.copy()
            rng.shuffle(shuffled)
            candidate = maximalize(n, tuple(candidate_rows), shuffled)
        retained.add(candidate)
        candidate_score = score(candidate)
        if candidate_score <= current_score or rng.random() < 0.04:
            current, current_score = candidate, candidate_score
    return sorted(retained)


def build_report(maximal_n: int = 5, adversarial_through: int = 15, attempts: int = 64) -> dict:
    exact = []
    for n in range(2, maximal_n + 1):
        exact.append(_summary(n, "all inclusion-maximal sets", [rows for rows, _ in maximal_profiles(n)]))
    adversarial = []
    for n in range(max(6, maximal_n + 1), adversarial_through + 1):
        sample_rows = set()
        # The universal and literal-all readings are already exactly false at n=3.
        for choice in ("shortest_lex", "minimum_turns"):
            sample_rows.update(
                adversarial_turning_witnesses(
                    n, attempts, 104729 + 1009 * n, choice
                )
            )
        adversarial.append(
            _summary(n, "turn-margin adversarial maximal sets", sorted(sample_rows))
        )
    return {
        "scope": "finite computational evidence only; no proof claim",
        "canonical_rule": "minimize (circuit edge count, sorted undirected edge list)",
        "resource_conventions": {
            "cells": "unit cells whose centers lie strictly inside the circuit",
            "rows": "vertex rows met by the circuit",
            "boundary_units": "unit perimeter edges used by the circuit",
            "U_components": "components of G[U] containing circuit vertices",
        },
        "target": "3|F|+c(G[U])+3 <= n^2+3n",
        "weighted_inequality": {
            "status": "false: minimum-turn counterexample at n=9",
            "statement": "T+7|F|+c(G[U])+3 <= 5n^2+3n",
            "T": (
                "total direction changes after selecting one circuit per owner; "
                "the promoted variant uses shortest_lex"
            ),
            "equivalent_margin": "strengthened_margin-(T-4|U|)",
            "implication": "T>=4|U| for rectilinear simple circuits gives the target",
            "quantifiers_tested": {
                "shortest_lex": "selected canonical circuit per owner",
                "minimum_turns": "minimum-turn circuit per owner",
                "maximum_turns": "universal over all choices, via per-owner maxima",
                "all_circuits": "literal sum over every owner-labelled circuit",
            },
        },
        "exact": exact,
        "adversarial": adversarial,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--maximal-n", type=int, default=5)
    parser.add_argument("--adversarial-through", type=int, default=15)
    parser.add_argument("--attempts", type=int, default=64)
    parser.add_argument(
        "--require-choice",
        choices=("shortest_lex", "minimum_turns", "maximum_turns", "all_circuits"),
        default="shortest_lex",
        help="exit nonzero if this interpretation has a negative sampled margin",
    )
    args = parser.parse_args()
    report = build_report(args.maximal_n, args.adversarial_through, args.attempts)
    print(json.dumps(report, indent=2))
    records = report["exact"] + report["adversarial"]
    if any(
        item["turning_quantifiers"][args.require_choice]["minimum_margin"] < 0
        for item in records
    ):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
