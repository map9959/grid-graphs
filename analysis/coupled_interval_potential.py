#!/usr/bin/env python3
"""Exact falsification gate for a coupled frontier interval potential.

The path weight ``n + 3 - 3*|F_row|`` sums to ``W + 2 - n``.  Therefore the
terminal target is four at every width for the desired universal ``W >= n+2``.
The projected state retains both active component partitions and all contiguous
interval rank profiles, but no absolute component names.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter, deque
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path

from coupled_forced_forest_row_grammar import (
    CoupledState,
    coupled_transition,
    first_coupled_row_state,
)


Feature = tuple


@dataclass(frozen=True)
class Edge:
    width: int
    row: int
    incoming: CoupledState | None
    outgoing: CoupledState
    mask: int
    weight: int


@dataclass
class Source:
    width: int
    layers: list[set[CoupledState | None]]
    edges: list[list[Edge]]


def enumerate_source(width: int) -> Source:
    layers: list[set[CoupledState | None]] = [{None}]
    edges: list[list[Edge]] = []
    for row in range(width):
        outgoing = set()
        row_edges = []
        for incoming in layers[-1]:
            for mask in range(1 << width):
                if incoming is None:
                    state = first_coupled_row_state(width, mask)
                else:
                    result = coupled_transition(width, incoming, mask)
                    state = None if result is None else result.state
                if state is None:
                    continue
                outgoing.add(state)
                row_edges.append(Edge(width, row, incoming, state, mask,
                                      width + 3 - 3 * mask.bit_count()))
        layers.append(outgoing)
        edges.append(row_edges)
    return Source(width, layers, edges)


def _runs(mask: int, width: int) -> int:
    return sum(
        bool(mask & (1 << column))
        and (column == 0 or not mask & (1 << (column - 1)))
        for column in range(width)
    )


def _rank(partition: tuple[int, ...], left: int, right: int) -> int:
    return len({label for label in partition[left:right] if label >= 0})


def interval_feature(
    width: int, row: int, state: CoupledState | None, level: str = "full"
) -> Feature:
    if state is None:
        return ("initial",)
    boundary = "terminal" if row == width else "top" if row == 1 else "interior"
    reserve: int | str = "terminal" if row == width else min(row, 6)
    interval_profiles = Counter()
    maxima: dict[tuple[int, int], int] = {}
    for left in range(width):
        forced = 0
        for right in range(left + 1, width + 1):
            forced += bool(state.forced_mask & (1 << (right - 1)))
            h_rank = _rank(state.h_partition, left, right)
            f_rank = _rank(state.f_partition, left, right)
            endpoint_mode = (
                int(bool(state.forced_mask & (1 << left))),
                int(bool(state.forced_mask & (1 << (right - 1)))),
            )
            deficit = h_rank + f_rank - forced
            interval_profiles[(right - left, forced, h_rank, f_rank, *endpoint_mode)] += 1
            maxima[endpoint_mode] = max(maxima.get(endpoint_mode, -width), deficit)
    base = (
        row % 3,
        boundary,
        reserve,
        width,
        state.forced_mask.bit_count(),
        _runs(state.forced_mask, width),
        int(bool(state.forced_mask & 1)),
        int(bool(state.forced_mask & (1 << (width - 1)))),
        len(set(state.h_partition)),
        len({label for label in state.f_partition if label >= 0}),
        state.retired_h,
        state.retired_f,
        state.forced_boundary_deficiency,
        tuple(sorted(maxima.items())),
    )
    if level == "extrema":
        return base
    if level == "full":
        return (*base, tuple(sorted(interval_profiles.items())))
    raise ValueError("level must be extrema or full")


def solve(
    sources: list[Source], level: str = "full", return_potentials: bool = False
) -> dict:
    zero: Feature = ("zero",)
    initial: Feature = ("initial",)
    vertices = {zero, initial}
    constraints: dict[tuple[Feature, Feature], tuple[int, Edge | None]] = {}

    def retain(u: Feature, v: Feature, weight: int, edge: Edge | None) -> None:
        old = constraints.get((u, v))
        if old is None or weight < old[0]:
            constraints[(u, v)] = weight, edge
        vertices.update((u, v))

    retain(zero, initial, 0, None)
    retain(initial, zero, 0, None)
    terminal_features = {}
    for source in sources:
        terminals = {
            interval_feature(source.width, source.width, state, level)
            for state in source.layers[-1]
            if state is not None
        }
        terminal_features[source.width] = terminals
        for terminal in terminals:
            retain(terminal, zero, -4, None)
        for row_edges in source.edges:
            for edge in row_edges:
                retain(
                    interval_feature(edge.width, edge.row, edge.incoming, level),
                    interval_feature(edge.width, edge.row + 1, edge.outgoing, level),
                    edge.weight,
                    edge,
                )

    adjacency = {vertex: [] for vertex in vertices}
    for (u, v), (weight, edge) in constraints.items():
        adjacency[u].append((v, weight, edge))
    distances = {vertex: 0 for vertex in vertices}
    predecessor = {}
    path_length = {vertex: 0 for vertex in vertices}
    queue = deque(vertices)
    queued = set(vertices)
    changed = None
    while queue and changed is None:
        u = queue.popleft()
        queued.remove(u)
        for v, weight, edge in adjacency[u]:
            candidate = distances[u] + weight
            if candidate >= distances[v]:
                continue
            distances[v] = candidate
            predecessor[v] = (u, edge, weight)
            path_length[v] = path_length[u] + 1
            if path_length[v] >= len(vertices):
                changed = v
                break
            if v not in queued:
                queue.append(v)
                queued.add(v)
    if changed is not None:
        cursor = changed
        for _ in vertices:
            cursor = predecessor[cursor][0]
        cycle = []
        start = cursor
        while True:
            u, edge, weight = predecessor[cursor]
            cycle.append((u, cursor, weight, edge))
            cursor = u
            if cursor == start:
                break
        return {
            "feasible": False,
            "feature_states": len(vertices) - 1,
            "constraints": len(constraints),
            "negative_cycle_weight": sum(item[2] for item in cycle),
            "counterexample": [
                None if edge is None else {
                    "width": edge.width,
                    "row": edge.row,
                    "mask": edge.mask,
                    "weight": edge.weight,
                    "incoming": None if edge.incoming is None else {
                        "mask": edge.incoming.forced_mask,
                        "h": edge.incoming.h_partition,
                        "f": edge.incoming.f_partition,
                    },
                    "outgoing": {
                        "mask": edge.outgoing.forced_mask,
                        "h": edge.outgoing.h_partition,
                        "f": edge.outgoing.f_partition,
                    },
                    "incoming_feature": interval_feature(
                        edge.width, edge.row, edge.incoming, level
                    ),
                    "outgoing_feature": interval_feature(
                        edge.width, edge.row + 1, edge.outgoing, level
                    ),
                }
                for _u, _v, _weight, edge in reversed(cycle)
            ],
        }
    shift = distances[zero]
    potentials = {state: value - shift for state, value in distances.items()}
    digest = hashlib.sha256()
    for state, value in sorted(potentials.items(), key=lambda item: repr(item[0])):
        digest.update(repr((state, value)).encode("ascii"))
    result = {
        "feasible": True,
        "feature_states": len(vertices) - 1,
        "constraints": len(constraints),
        "potential_range": [min(potentials.values()), max(potentials.values())],
        "terminal_minima": {
            str(width): min(potentials[state] for state in terminals)
            for width, terminals in terminal_features.items()
        },
        "potential_sha256": digest.hexdigest(),
    }
    if return_potentials:
        result["potential_values"] = sorted(potentials.items(), key=lambda item: repr(item[0]))
    return result


def experiment(widths: list[int], level: str = "full") -> dict:
    sources = [enumerate_source(width) for width in widths]
    return {
        "scope": {
            "widths": widths,
            "terminal_target": 4,
            "feature_level": level,
            "semantics": "finite-width exact falsification gate, not a uniform proof",
        },
        "census": {
            str(source.width): {
                "states_by_layer": [len(layer) for layer in source.layers],
                "transitions_by_row": [len(edges) for edges in source.edges],
            }
            for source in sources
        },
        "result": solve(sources, level),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--widths", type=int, nargs="+", default=[3, 4, 5, 6])
    parser.add_argument("--output", type=Path)
    parser.add_argument("--level", choices=("extrema", "full"), default="full")
    args = parser.parse_args()
    result = experiment(sorted(set(args.widths)), args.level)
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(rendered)
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
