#!/usr/bin/env python3
"""Finite-width CEGAR diagnostics for residue-two equality states.

The experiment uses every state and edge in the exact n=5 and n=8 minimum
corridors.  It is an observational collision audit, not a proof that any
candidate quotient works at unenumerated widths.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Iterable

from analysis.tiles.tile_grammar import FrontierState
from analysis.transport.equality_corridor import (
    CorridorEdge,
    EqualityCorridor,
    build_equality_corridor,
)

SCHEMA = "grid-graphs.residue-two-equality-cegar.v1"
WIDTHS = (5, 8)
LEVELS = ("coarse", "attachment", "exact")


def _runs(mask: int) -> int:
    return (mask & ~(mask << 1)).bit_count()


def _intervals(values: tuple[int, ...], target: int) -> int:
    return sum(
        value == target and (index == 0 or values[index - 1] != target)
        for index, value in enumerate(values)
    )


def _boundary_mode(state: FrontierState) -> str:
    if state.row_index == 0:
        return "top"
    if state.row_index == state.n:
        return "terminal"
    if state.row_index + 1 == state.n:
        return "bottom"
    return "bulk"


def _coarse_key(state: FrontierState) -> tuple:
    """Packet-normalized run, OUT, and attachment-debt fields."""
    packets = state.n // 3
    active_packets = packets if len(state.partition) > 1 else 0
    mask = state.previous_u_mask
    faces = state.partition[1:]
    out = state.partition[0]
    non_out = set(faces) - {out}
    return (
        state.row_index % 3,
        _boundary_mode(state),
        mask.bit_count() - 2 * active_packets,
        _runs(mask) - active_packets,
        bool(mask & 1),
        bool(mask & (1 << (state.n - 1))),
        len(faces) - sum(label == out for label in faces) - 3 * active_packets,
        _intervals(faces, out),
        bool(faces and faces[0] == out),
        bool(faces and faces[-1] == out),
        len(non_out) - 3 * active_packets,
    )


def _attachment_profiles(state: FrontierState) -> tuple:
    faces = state.partition[1:]
    out = state.partition[0]
    profiles = []
    for label in set(faces) - {out}:
        slots = tuple(index for index, value in enumerate(faces) if value == label)
        profiles.append(
            (
                len(slots),
                _intervals(faces, label),
                bool(slots and slots[0] == 0),
                bool(slots and slots[-1] + 1 == len(faces)),
            )
        )
    return tuple(sorted(profiles))


def abstract_key(state: FrontierState, level: str) -> tuple:
    """Return one key in the declared coarse-to-exact refinement hierarchy."""
    if level == "coarse":
        return _coarse_key(state)
    if level == "attachment":
        return (*_coarse_key(state), _attachment_profiles(state))
    if level == "exact":
        # This final, deliberately width-specific level is a control: unlike
        # the candidate levels it makes no width-independent quotient claim.
        return (state.n, state.row_index, state.previous_u_mask, state.partition)
    raise ValueError(f"unknown abstraction level: {level}")


def transition_behavior_label(edge: CorridorEdge, n: int) -> tuple:
    """Width-normalized observable label for one equality-corridor edge."""
    packets = n // 3
    return (
        (edge.row + 1) % 3,
        edge.d_u - 2 * packets,
        edge.horizontal_runs - packets,
        edge.vertical_edges - 2 * packets,
        edge.d_rank - 3 * packets,
        edge.d_cycles,
        edge.weight,
        bool(edge.mask & 1),
        bool(edge.mask & (1 << (n - 1))),
    )


def state_id(n: int, key: tuple[int, int, tuple[int, ...]]) -> str:
    row, mask, partition = key
    return f"n{n}:r{row}:m{mask:x}:p{'.'.join(map(str, partition))}"


@dataclass(frozen=True, slots=True)
class ObservedState:
    identifier: str
    width: int
    state: FrontierState
    outgoing_labels: frozenset[tuple]
    accepting_suffixes: frozenset[tuple[tuple, ...]]

    @property
    def behavior(self) -> tuple[frozenset[tuple], frozenset[tuple[tuple, ...]]]:
        return self.outgoing_labels, self.accepting_suffixes


def observe_corridor(corridor: EqualityCorridor) -> list[ObservedState]:
    """Observe complete one-step and accepting-suffix behavior in a corridor."""
    by_incoming = []
    for edges in corridor.corridor_edges:
        grouped: dict[tuple, list[CorridorEdge]] = defaultdict(list)
        for edge in edges:
            grouped[edge.incoming].append(edge)
        by_incoming.append(grouped)

    suffixes: list[dict[tuple, frozenset[tuple[tuple, ...]]]] = [
        {} for _ in range(corridor.n + 1)
    ]
    suffixes[corridor.n] = {
        key: frozenset({()}) for key in corridor.corridor_states[corridor.n]
    }
    outgoing: dict[tuple, frozenset[tuple]] = {}
    for row in reversed(range(corridor.n)):
        for key in corridor.corridor_states[row]:
            edges = by_incoming[row][key]
            labels = frozenset(
                transition_behavior_label(edge, corridor.n) for edge in edges
            )
            outgoing[key] = labels
            words = {
                (transition_behavior_label(edge, corridor.n), *suffix)
                for edge in edges
                for suffix in suffixes[row + 1][edge.outgoing]
            }
            suffixes[row][key] = frozenset(words)

    observations = []
    for row, keys in enumerate(corridor.corridor_states):
        for key in keys:
            observations.append(
                ObservedState(
                    state_id(corridor.n, key),
                    corridor.n,
                    corridor.layers[row][key],
                    outgoing.get(key, frozenset()),
                    suffixes[row][key],
                )
            )
    return sorted(observations, key=lambda item: item.identifier)


def _jsonable(value):
    if isinstance(value, (tuple, list)):
        return [_jsonable(item) for item in value]
    if isinstance(value, (set, frozenset)):
        return [_jsonable(item) for item in sorted(value, key=repr)]
    return value


def _digest(value) -> str:
    payload = json.dumps(_jsonable(value), separators=(",", ":"), sort_keys=True)
    return hashlib.sha256(payload.encode("ascii")).hexdigest()[:16]


def _witness(left: ObservedState, right: ObservedState) -> dict:
    return {
        "state_ids": [left.identifier, right.identifier],
        "widths": [left.width, right.width],
        "outgoing_labels_differ": left.outgoing_labels != right.outgoing_labels,
        "accepting_suffixes_differ": left.accepting_suffixes != right.accepting_suffixes,
        "behaviors": [
            {
                "outgoing_label_count": len(item.outgoing_labels),
                "accepting_suffix_count": len(item.accepting_suffixes),
                "digest": _digest(item.behavior),
            }
            for item in (left, right)
        ],
    }


def _differing_pair(
    states: list[ObservedState], predicate: Callable[[ObservedState, ObservedState], bool]
) -> tuple[ObservedState, ObservedState] | None:
    for index, left in enumerate(states):
        for right in states[index + 1 :]:
            if predicate(left, right) and left.behavior != right.behavior:
                return left, right
    return None


def collision_report(observations: Iterable[ObservedState], level: str) -> dict:
    """Group states by one key and report every behavior-inconsistent group."""
    groups: dict[tuple, list[ObservedState]] = defaultdict(list)
    for observed in observations:
        groups[abstract_key(observed.state, level)].append(observed)

    records = []
    merged_groups = 0
    cross_width_groups = 0
    bulk_cross_width_groups = 0
    within_width_groups = 0
    for key, states in sorted(groups.items(), key=lambda item: repr(item[0])):
        states.sort(key=lambda item: item.identifier)
        if len(states) > 1:
            merged_groups += 1
        if len({item.behavior for item in states}) == 1:
            continue
        cross = _differing_pair(states, lambda left, right: left.width != right.width)
        bulk_cross = _differing_pair(
            states,
            lambda left, right: (
                left.width != right.width
                and _boundary_mode(left.state) == "bulk"
                and _boundary_mode(right.state) == "bulk"
            ),
        )
        within = _differing_pair(states, lambda left, right: left.width == right.width)
        cross_width_groups += cross is not None
        bulk_cross_width_groups += bulk_cross is not None
        within_width_groups += within is not None
        records.append(
            {
                "abstract_key": _jsonable(key),
                "state_count": len(states),
                "widths": sorted({item.width for item in states}),
                "behavior_classes": len({item.behavior for item in states}),
                "cross_width_witness": _witness(*cross) if cross else None,
                "within_width_witness": _witness(*within) if within else None,
            }
        )
    return {
        "keys": len(groups),
        "merged_groups": merged_groups,
        "collision_groups": len(records),
        "cross_width_collision_groups": cross_width_groups,
        "bulk_cross_width_collision_groups": bulk_cross_width_groups,
        "within_width_collision_groups": within_width_groups,
        "collisions": records,
    }


def build_artifact() -> dict:
    corridors = {n: build_equality_corridor(n) for n in WIDTHS}
    by_width = {n: observe_corridor(corridor) for n, corridor in corridors.items()}
    observations = [item for n in WIDTHS for item in by_width[n]]
    hierarchy = {level: collision_report(observations, level) for level in LEVELS}
    if hierarchy["exact"]["collision_groups"]:
        raise AssertionError("the exact structural control unexpectedly collided")
    return {
        "schema": SCHEMA,
        "scope": {
            "semantics": "finite-width-complete-equality-corridor-diagnostic-only",
            "widths": list(WIDTHS),
            "theorem_or_certificate": False,
            "coverage_beyond_enumerated_widths_claimed": False,
        },
        "definitions": {
            "state_behavior": "complete set of outgoing normalized equality-edge labels together with the complete set of accepting suffix label words",
            "cross_width_collision": "one abstract key contains differing behaviors witnessed at different widths",
            "within_width_collision": "one abstract key contains differing behaviors witnessed at the same width",
            "hierarchy": list(LEVELS),
            "exact_control": "(width, row, previous U mask, rooted structural partition); deliberately not width-independent",
        },
        "corridors": {
            str(n): {
                "minimum_weight": corridors[n].minimum_weight,
                "minimum_path_count": str(corridors[n].minimum_path_count),
                "states": len(by_width[n]),
                "transitions": sum(map(len, corridors[n].corridor_edges)),
                "states_by_row": [len(layer) for layer in corridors[n].corridor_states],
                "transitions_by_row": [len(layer) for layer in corridors[n].corridor_edges],
            }
            for n in WIDTHS
        },
        "observations": {
            "states": len(observations),
            "outgoing_equality_transitions": sum(
                len(edges) for corridor in corridors.values() for edges in corridor.corridor_edges
            ),
        },
        "hierarchy": hierarchy,
        "provenance": {
            "producer": "analysis/residue_certificates/residue_two_equality_cegar.py",
            "command": [
                "python3",
                "-B",
                "-m",
                'analysis.residue_certificates.residue_two_equality_cegar',
                "--output",
                "analysis/residue_two_equality_cegar.json",
            ],
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    artifact = build_artifact()
    rendered = json.dumps(artifact, indent=2, sort_keys=True) + "\n"
    if args.check:
        if args.output is None or not args.output.exists() or args.output.read_text() != rendered:
            raise SystemExit(f"stale or missing artifact: {args.output}")
        print(f"exact CEGAR diagnostic matches {args.output}")
    else:
        if args.output is not None:
            args.output.write_text(rendered)
        print(rendered, end="")


if __name__ == "__main__":
    main()
