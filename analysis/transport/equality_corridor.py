#!/usr/bin/env python3
"""Represent every exact minimum-curvature path by its frontier corridor."""

from __future__ import annotations

import argparse
import json
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import TypeAlias

from analysis.bounds.proof_oriented_identities import frontier_feature_signature, tile_grammar_row_deltas
from analysis.tiles.tile_grammar import FrontierState, advance_row, initial_state


StateKey: TypeAlias = tuple[int, int, tuple[int, ...]]
SCHEMA = "grid-graphs.equality-corridor.v1"


@dataclass(frozen=True, slots=True)
class CorridorEdge:
    row: int
    incoming: StateKey
    outgoing: StateKey
    mask: int
    d_u: int
    d_rank: int
    d_cycles: int
    horizontal_runs: int
    vertical_edges: int
    weight: int


@dataclass(slots=True)
class EqualityCorridor:
    n: int
    minimum_weight: int
    minimum_u: int
    layers: list[dict[StateKey, FrontierState]]
    forward: list[dict[StateKey, int]]
    backward: list[dict[StateKey, int]]
    corridor_states: list[set[StateKey]]
    corridor_edges: list[list[CorridorEdge]]
    attempted_by_row: list[int]
    accepted_by_row: list[int]
    minimum_path_count: int


def structural_key(state: FrontierState) -> StateKey:
    return state.row_index, state.previous_u_mask, state.partition


def _edge(
    row: int,
    incoming_key: StateKey,
    incoming: FrontierState,
    mask: int,
    outgoing: FrontierState,
) -> CorridorEdge:
    deltas = tile_grammar_row_deltas(incoming, mask, outgoing)
    return CorridorEdge(
        row=row,
        incoming=incoming_key,
        outgoing=structural_key(outgoing),
        mask=mask,
        d_u=deltas.u_count,
        d_rank=deltas.rank_delta,
        d_cycles=deltas.cycle_delta,
        horizontal_runs=deltas.horizontal_runs,
        vertical_edges=deltas.vertical_edges,
        weight=3 * deltas.u_count - 2 * deltas.rank_delta - 1,
    )


def build_equality_corridor(n: int) -> EqualityCorridor:
    """Compute exact forward/backward distances and all globally minimum edges."""
    if n < 2 or n > 8:
        raise ValueError("equality-corridor prototype supports 2 <= n <= 8")
    initial = initial_state(n)
    initial_key = structural_key(initial)
    layers = [{initial_key: initial}]
    forward = [{initial_key: 0}]
    attempted_by_row = []
    accepted_by_row = []

    for row in range(n):
        children: dict[StateKey, FrontierState] = {}
        child_distances: dict[StateKey, int] = {}
        attempted = accepted = 0
        for incoming_key, incoming in layers[row].items():
            if structural_key(incoming) != incoming_key:
                raise AssertionError("representative does not match its structural key")
            for mask in range(1 << n):
                attempted += 1
                outgoing = advance_row(incoming, mask)
                if outgoing is None:
                    continue
                accepted += 1
                edge = _edge(row, incoming_key, incoming, mask, outgoing)
                candidate = forward[row][incoming_key] + edge.weight
                previous = child_distances.get(edge.outgoing)
                if previous is None or candidate < previous:
                    child_distances[edge.outgoing] = candidate
                children.setdefault(edge.outgoing, outgoing)
        layers.append(children)
        forward.append(child_distances)
        attempted_by_row.append(attempted)
        accepted_by_row.append(accepted)

    if not layers[n] or any(key[0] != n or key[2] != (0,) for key in layers[n]):
        raise AssertionError("terminal layer is empty or contains a disconnected state")
    minimum_weight = min(forward[n].values())
    numerator = minimum_weight + n + 2 * (n - 1) ** 2
    if numerator % 3:
        raise AssertionError("minimum curvature does not determine an integral U count")
    minimum_u = numerator // 3

    backward: list[dict[StateKey, int]] = [{} for _ in range(n + 1)]
    backward[n] = {key: 0 for key in layers[n]}
    corridor_edges: list[list[CorridorEdge]] = [[] for _ in range(n)]
    for row in reversed(range(n)):
        distances: dict[StateKey, int] = {}
        for incoming_key, incoming in layers[row].items():
            best = None
            for mask in range(1 << n):
                outgoing = advance_row(incoming, mask)
                if outgoing is None:
                    continue
                edge = _edge(row, incoming_key, incoming, mask, outgoing)
                remaining = backward[row + 1].get(edge.outgoing)
                if remaining is None:
                    continue
                candidate = edge.weight + remaining
                best = candidate if best is None else min(best, candidate)
                if forward[row][incoming_key] + candidate == minimum_weight:
                    corridor_edges[row].append(edge)
            if best is not None:
                distances[incoming_key] = best
        backward[row] = distances

    if backward[0].get(initial_key) != minimum_weight:
        raise AssertionError("forward and backward minimum weights disagree")
    corridor_states = [
        {
            key
            for key, prefix in forward[row].items()
            if key in backward[row] and prefix + backward[row][key] == minimum_weight
        }
        for row in range(n + 1)
    ]
    for row, edges in enumerate(corridor_edges):
        for edge in edges:
            if edge.incoming not in corridor_states[row] or edge.outgoing not in corridor_states[row + 1]:
                raise AssertionError("corridor edge has a non-corridor endpoint")

    path_counts = {initial_key: 1}
    for row, edges in enumerate(corridor_edges):
        outgoing_counts: dict[StateKey, int] = {}
        for edge in edges:
            outgoing_counts[edge.outgoing] = (
                outgoing_counts.get(edge.outgoing, 0) + path_counts.get(edge.incoming, 0)
            )
        path_counts = outgoing_counts
        if set(path_counts) != corridor_states[row + 1]:
            raise AssertionError("corridor path counts do not cover the next state layer")
    minimum_path_count = sum(path_counts.values())

    return EqualityCorridor(
        n=n,
        minimum_weight=minimum_weight,
        minimum_u=minimum_u,
        layers=layers,
        forward=forward,
        backward=backward,
        corridor_states=corridor_states,
        corridor_edges=corridor_edges,
        attempted_by_row=attempted_by_row,
        accepted_by_row=accepted_by_row,
        minimum_path_count=minimum_path_count,
    )


def _state_metadata(state: FrontierState) -> dict:
    return {
        "row_index": state.row_index,
        "previous_u_mask": state.previous_u_mask,
        "partition": state.partition,
    }


def _state_profile(state: FrontierState) -> tuple:
    return frontier_feature_signature(state.n, _state_metadata(state), "profiles")


def _transition_profile(
    corridor: EqualityCorridor, edge: CorridorEdge
) -> tuple:
    incoming = corridor.layers[edge.row][edge.incoming]
    outgoing = corridor.layers[edge.row + 1][edge.outgoing]
    incoming_profile = _state_profile(incoming)
    outgoing_profile = _state_profile(outgoing)
    return (
        (edge.row + 1) % 3,
        incoming_profile[1],
        outgoing_profile[1],
        incoming_profile[2],
        incoming_profile[9],
        edge.d_u,
        edge.horizontal_runs,
        edge.vertical_edges,
        edge.d_cycles,
        edge.d_rank,
        edge.weight,
        incoming_profile[5],
        outgoing_profile[5],
        incoming_profile[6],
        outgoing_profile[6],
        incoming_profile[10],
        outgoing_profile[10],
        int(incoming_profile[7]) + int(incoming_profile[8]),
        int(outgoing_profile[7]) + int(outgoing_profile[8]),
    )


def normalized_state_profile(state: FrontierState, level: str = "full") -> tuple:
    """Normalize density by two U vertices per width-three packet."""
    if level not in ("packet", "overlap", "local", "transport", "attachment", "full"):
        raise ValueError("unknown normalized profile level")
    profile = frontier_feature_signature(state.n, _state_metadata(state), "out")
    active_faces = 0 if profile[1] in ("top", "terminal") else state.n - 1
    packets = state.n // 3
    transport = (
        profile[0],
        profile[1],
        profile[2] - 2 * packets,
        profile[9],
        profile[3],
        profile[4],
    )
    if level in ("packet", "overlap", "local", "transport"):
        return transport
    attachment = (
        *transport,
        profile[5],
        profile[6] - active_faces,
        profile[7],
        profile[8],
        profile[10],
    )
    if level == "attachment":
        return attachment
    return (*attachment, active_faces - profile[5], profile[6])


def normalized_transition_profile(
    incoming: FrontierState,
    outgoing: FrontierState,
    edge: CorridorEdge,
    level: str = "full",
) -> tuple:
    packets = incoming.n // 3
    packet = (
        (edge.row + 1) % 3,
        normalized_state_profile(incoming, "transport")[1],
        normalized_state_profile(outgoing, "transport")[1],
        edge.d_u - 2 * packets,
        edge.horizontal_runs,
    )
    if level == "packet":
        return packet
    overlap = (
        *packet,
        edge.vertical_edges - 2 * packets,
    )
    if level == "overlap":
        return overlap
    local = (
        *overlap,
        edge.d_cycles,
        edge.weight,
    )
    if level == "local":
        return local
    return (
        normalized_state_profile(incoming, level),
        normalized_state_profile(outgoing, level),
        edge.d_u - 2 * packets,
        edge.horizontal_runs,
        edge.vertical_edges - 2 * packets,
        edge.d_cycles,
        edge.weight,
    )


def _normalized_corridor_support(
    corridor: EqualityCorridor, level: str
) -> tuple[set[tuple], set[tuple]]:
    states = {
        normalized_state_profile(corridor.layers[row][key], level)
        for row, keys in enumerate(corridor.corridor_states)
        for key in keys
    }
    transitions = {
        normalized_transition_profile(
            corridor.layers[edge.row][edge.incoming],
            corridor.layers[edge.row + 1][edge.outgoing],
            edge,
            level,
        )
        for edges in corridor.corridor_edges
        for edge in edges
    }
    return states, transitions


def _trace_profiles(rows: list[str], level: str) -> tuple[list[tuple], list[int]]:
    from analysis.tiles.tile_grammar import row_mask

    n = len(rows)
    state = initial_state(n)
    profiles = []
    weights = []
    for row_index, row in enumerate(rows):
        mask = row_mask(row)
        outgoing = advance_row(state, mask)
        if outgoing is None:
            raise ValueError("trace seals a dual component or is not connected")
        edge = _edge(row_index, structural_key(state), state, mask, outgoing)
        profiles.append(normalized_transition_profile(state, outgoing, edge, level))
        weights.append(edge.weight)
        state = outgoing
    return profiles, weights


def residue_two_comparison() -> dict:
    """Compare exact n=5,8 equality corridors with known n=14,17 traces."""
    from analysis.patterns.diagonal_patterns import residue_two_affine_pattern, residue_two_explicit_pattern

    corridors = {n: build_equality_corridor(n) for n in (5, 8)}
    levels = ("packet", "overlap", "local", "transport", "attachment", "full")
    supports = {
        level: {
            n: _normalized_corridor_support(corridor, level)
            for n, corridor in corridors.items()
        }
        for level in levels
    }

    traces = {str(n): {} for n in (14, 17)}
    for n, rows in (
        (14, residue_two_explicit_pattern(14)),
        (17, residue_two_affine_pattern(17)),
    ):
        for level in levels:
            profiles, weights = _trace_profiles(rows, level)
            baseline_transitions = supports[level][5][1] | supports[level][8][1]
            matched_rows = [
                index for index, profile in enumerate(profiles) if profile in baseline_transitions
            ]
            traces[str(n)][level] = {
                "matched_baseline_rows": matched_rows,
                "unmatched_baseline_rows": [
                    index for index in range(n) if index not in set(matched_rows)
                ],
            }
        traces[str(n)]["row_weights"] = weights
        traces[str(n)]["total_weight"] = sum(weights)

    return {
        "schema": "grid-graphs.residue-two-equality-comparison.v1",
        "scope": {
            "baseline_widths": [5, 8],
            "trace_widths": [14, 17],
            "semantics": "normalized-profile-diagnostic-only",
        },
        "corridors": {
            str(n): {
                "minimum_weight": corridor.minimum_weight,
                "minimum_u": corridor.minimum_u,
                "minimum_path_count": str(corridor.minimum_path_count),
                "corridor_states_by_row": [len(layer) for layer in corridor.corridor_states],
                "corridor_transitions_by_row": [len(layer) for layer in corridor.corridor_edges],
                "normalized_profiles": {
                    level: {
                        "states": len(supports[level][n][0]),
                        "transitions": len(supports[level][n][1]),
                    }
                    for level in levels
                },
            }
            for n, corridor in corridors.items()
        },
        "normalized_overlap": {
            level: {
                "state_profiles": len(supports[level][5][0] & supports[level][8][0]),
                "transition_profiles": len(supports[level][5][1] & supports[level][8][1]),
            }
            for level in levels
        },
        "traces": traces,
        "provenance": {
            "producer": "analysis/transport/equality_corridor.py",
            "command": [
                "python3",
                "-B",
                "analysis/transport/equality_corridor.py",
                "--compare-residue-two",
                "--output",
                "analysis/residue_two_equality_comparison.json",
            ],
        },
    }


def _counter_records(counter: Counter[tuple]) -> list[dict]:
    return [
        {"profile": profile, "count": count}
        for profile, count in sorted(counter.items(), key=lambda item: repr(item[0]))
    ]


def corridor_summary(corridor: EqualityCorridor) -> dict:
    state_profiles = Counter(
        _state_profile(corridor.layers[row][key])
        for row, keys in enumerate(corridor.corridor_states)
        for key in keys
    )
    transition_profiles = Counter(
        _transition_profile(corridor, edge)
        for edges in corridor.corridor_edges
        for edge in edges
    )
    weight_histogram = Counter(
        edge.weight for edges in corridor.corridor_edges for edge in edges
    )
    return {
        "schema": SCHEMA,
        "scope": {
            "semantics": "complete-reachable-row-quotient",
            "n": corridor.n,
            "row_charge": 1,
        },
        "minimum_weight": corridor.minimum_weight,
        "minimum_u": corridor.minimum_u,
        "minimum_path_count": str(corridor.minimum_path_count),
        "census": {
            "reachable_states_by_row": [len(layer) for layer in corridor.layers],
            "attempted_transitions_by_row": corridor.attempted_by_row,
            "accepted_transitions_by_row": corridor.accepted_by_row,
            "corridor_states_by_row": [len(layer) for layer in corridor.corridor_states],
            "corridor_transitions_by_row": [len(layer) for layer in corridor.corridor_edges],
            "unique_state_profiles": len(state_profiles),
            "unique_transition_profiles": len(transition_profiles),
            "corridor_weight_histogram": {
                str(weight): count for weight, count in sorted(weight_histogram.items())
            },
        },
        "state_profiles": _counter_records(state_profiles),
        "transition_profiles": _counter_records(transition_profiles),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--n", type=int, choices=range(2, 9))
    group.add_argument("--compare-residue-two", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    summary = (
        residue_two_comparison()
        if args.compare_residue_two
        else corridor_summary(build_equality_corridor(args.n))
    )
    rendered = json.dumps(summary, indent=2) + "\n"
    if args.output is not None:
        args.output.write_text(rendered)
    print(rendered, end="")


if __name__ == "__main__":
    main()
