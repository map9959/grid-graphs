#!/usr/bin/env python3
"""Observed motif compression for selected residue-two equality frontiers.

This is a finite diagnostic, not a theorem or a certificate.  It covers every
state in the complete n=5 and n=8 equality corridors, one fixed equality
witness at n=11 and n=14, and the fixed 179-U n=17 near-equality control.
Only the two complete corridors support complete continuation comparisons.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path

from diagonal_patterns import residue_two_affine_pattern, residue_two_explicit_pattern
from equality_corridor import CorridorEdge, EqualityCorridor, build_equality_corridor
from tile_grammar import FrontierState, advance_row, initial_state, row_mask


SCHEMA = "grid-graphs.residue-two-equality-motifs.v1"
CORRIDOR_WIDTHS = (5, 8)
FIXED_WIDTHS = (11, 14, 17)
EVENT_ROLES = ("single", "open", "carry", "close")


def canonical_rooted_partition(partition: tuple[int, ...]) -> tuple[int, ...]:
    """Relabel by first occurrence, with the distinguished OUT block first."""
    if not partition:
        raise ValueError("a rooted partition must contain OUT")
    labels = {partition[0]: 0}
    result = []
    for label in partition:
        labels.setdefault(label, len(labels))
        result.append(labels[label])
    return tuple(result)


@dataclass(frozen=True, slots=True)
class IntervalEvent:
    component: int
    role: str


@dataclass(frozen=True, slots=True)
class EventWord:
    """A lossless rooted partition word, grouped into width-three packets."""

    width: int
    root_component: int
    packets: tuple[tuple[IntervalEvent, ...], ...]


def encode_event_word(width: int, partition: tuple[int, ...]) -> EventWord:
    """Encode component intervals as ordered open/carry/close packet events."""
    if width < 2:
        raise ValueError("width must be at least two")
    rooted = canonical_rooted_partition(partition)
    if len(rooted) not in (1, width):
        raise ValueError("partition must be initial/terminal or have one slot per width")
    faces = rooted[1:]
    occurrences: dict[int, list[int]] = defaultdict(list)
    for slot, component in enumerate(faces):
        occurrences[component].append(slot)
    events = []
    for slot, component in enumerate(faces):
        positions = occurrences[component]
        if len(positions) == 1:
            role = "single"
        elif slot == positions[0]:
            role = "open"
        elif slot == positions[-1]:
            role = "close"
        else:
            role = "carry"
        events.append(IntervalEvent(component, role))
    packets = tuple(tuple(events[start : start + 3]) for start in range(0, len(events), 3))
    return EventWord(width, 0, packets)


def decode_event_word(word: EventWord) -> tuple[int, ...]:
    """Decode and validate an event word back to its canonical partition."""
    events = tuple(event for packet in word.packets for event in packet)
    if len(events) not in (0, word.width - 1):
        raise ValueError("event word has the wrong number of frontier slots")
    if word.root_component != 0 or any(event.role not in EVENT_ROLES for event in events):
        raise ValueError("event word has an invalid root or role")
    partition = (word.root_component, *(event.component for event in events))
    if canonical_rooted_partition(partition) != partition:
        raise ValueError("event components are not canonically rooted")
    if encode_event_word(word.width, partition) != word:
        raise ValueError("event roles do not match their component intervals")
    return partition


def _intervals(word: EventWord) -> dict[int, tuple[int, int]]:
    slots: dict[int, list[int]] = defaultdict(list)
    for index, event in enumerate(event for packet in word.packets for event in packet):
        slots[event.component].append(index)
    return {component: (positions[0], positions[-1]) for component, positions in slots.items()}


def event_metrics(word: EventWord) -> dict:
    """Measure interval nesting/overlap, packet carry, and component spans."""
    intervals = _intervals(word)
    slot_count = sum(map(len, word.packets))
    depths = [
        sum(left <= slot <= right for left, right in intervals.values())
        for slot in range(slot_count)
    ]
    boundaries = range(3, slot_count, 3)
    carries = [
        sum(left < boundary <= right for left, right in intervals.values())
        for boundary in boundaries
    ]
    return {
        "max_stack_depth": max(depths, default=0),
        "carry_widths": tuple(carries),
        "component_spans": tuple(sorted(right - left + 1 for left, right in intervals.values())),
    }


def _boundary_mode(state: FrontierState) -> str:
    if state.row_index == 0:
        return "top"
    if state.row_index == state.n:
        return "terminal"
    if state.row_index + 1 == state.n:
        return "bottom"
    return "bulk"


def _packet_symbol(word: EventWord, packet_index: int) -> tuple:
    """Forget component names but retain rooted roles and boundary carry width."""
    packet = word.packets[packet_index]
    intervals = _intervals(word)
    left = packet_index * 3
    right = left + len(packet)
    carry_in = sum(start < left <= end for start, end in intervals.values())
    carry_out = sum(start < right <= end for start, end in intervals.values())
    return (
        tuple((event.role, event.component == word.root_component) for event in packet),
        carry_in,
        carry_out,
    )


def _run_length(values: tuple[tuple, ...]) -> tuple[tuple[tuple, int], ...]:
    runs: list[tuple[tuple, int]] = []
    for value in values:
        if runs and runs[-1][0] == value:
            runs[-1] = (value, runs[-1][1] + 1)
        else:
            runs.append((value, 1))
    return tuple(runs)


def motif_key(state: FrontierState, candidate: str) -> tuple:
    """Return an explicitly candidate, lossy packet-motif normalization."""
    word = encode_event_word(state.n, state.partition)
    symbols = tuple(_packet_symbol(word, index) for index in range(len(word.packets)))
    runs = _run_length(symbols)
    prefix = (state.row_index % 3, _boundary_mode(state))
    if candidate == "run_length":
        return (*prefix, runs)
    if candidate == "affine":
        # A repeated interior packet is treated as an affine, extensible run.
        return (*prefix, tuple((symbol, 1 if count == 1 else "2+") for symbol, count in runs))
    raise ValueError(f"unknown motif candidate: {candidate}")


def _transition_label(edge: CorridorEdge, width: int) -> tuple:
    packets = width // 3
    return (
        (edge.row + 1) % 3,
        edge.d_u - 2 * packets,
        edge.horizontal_runs - packets,
        edge.vertical_edges - 2 * packets,
        edge.d_rank - 3 * packets,
        edge.d_cycles,
        edge.weight,
        bool(edge.mask & 1),
        bool(edge.mask & (1 << (width - 1))),
    )


@dataclass(frozen=True, slots=True)
class CompleteObservation:
    identifier: str
    width: int
    state: FrontierState
    outgoing_labels: frozenset[tuple]
    accepting_suffixes: frozenset[tuple[tuple, ...]]

    @property
    def behavior(self) -> tuple:
        return self.outgoing_labels, self.accepting_suffixes


def observe_complete_continuations(corridor: EqualityCorridor) -> list[CompleteObservation]:
    """Compute exact observed continuation languages in one complete corridor."""
    outgoing_edges: list[dict[tuple, list[CorridorEdge]]] = []
    for edges in corridor.corridor_edges:
        grouped: dict[tuple, list[CorridorEdge]] = defaultdict(list)
        for edge in edges:
            grouped[edge.incoming].append(edge)
        outgoing_edges.append(grouped)
    suffixes: list[dict[tuple, frozenset[tuple[tuple, ...]]]] = [
        {} for _ in range(corridor.n + 1)
    ]
    suffixes[-1] = {key: frozenset({()}) for key in corridor.corridor_states[-1]}
    labels_by_state: dict[tuple, frozenset[tuple]] = {}
    for row in reversed(range(corridor.n)):
        for key in corridor.corridor_states[row]:
            edges = outgoing_edges[row][key]
            labels_by_state[key] = frozenset(_transition_label(edge, corridor.n) for edge in edges)
            suffixes[row][key] = frozenset(
                (_transition_label(edge, corridor.n), *suffix)
                for edge in edges
                for suffix in suffixes[row + 1][edge.outgoing]
            )
    observations = []
    for row, keys in enumerate(corridor.corridor_states):
        for key in keys:
            state = corridor.layers[row][key]
            observations.append(
                CompleteObservation(
                    f"n{corridor.n}:r{row}:m{state.previous_u_mask:x}:p{'.'.join(map(str, state.partition))}",
                    corridor.n,
                    state,
                    labels_by_state.get(key, frozenset()),
                    suffixes[row][key],
                )
            )
    return sorted(observations, key=lambda item: item.identifier)


def _digest(value) -> str:
    def jsonable(item):
        if isinstance(item, (tuple, list)):
            return [jsonable(child) for child in item]
        if isinstance(item, (set, frozenset)):
            return [jsonable(child) for child in sorted(item, key=repr)]
        return item

    payload = json.dumps(jsonable(value), separators=(",", ":"), sort_keys=True)
    return hashlib.sha256(payload.encode("ascii")).hexdigest()[:16]


def collision_report(observations: list[CompleteObservation], candidate: str) -> dict:
    """Audit one lossy motif key against complete observed continuation behavior."""
    groups: dict[tuple, list[CompleteObservation]] = defaultdict(list)
    for observation in observations:
        groups[motif_key(observation.state, candidate)].append(observation)
    collisions = []
    merged = cross_width = 0
    for key, states in sorted(groups.items(), key=lambda item: repr(item[0])):
        states.sort(key=lambda item: item.identifier)
        merged += len(states) > 1
        behaviors = {state.behavior for state in states}
        if len(behaviors) == 1:
            continue
        witness = next(
            (state for state in states[1:] if state.behavior != states[0].behavior),
            states[1],
        )
        cross_width += len({state.width for state in states}) > 1
        collisions.append(
            {
                "motif_digest": _digest(key),
                "state_count": len(states),
                "widths": sorted({state.width for state in states}),
                "behavior_classes": len(behaviors),
                "witnesses": [
                    {
                        "state_id": state.identifier,
                        "outgoing_labels": len(state.outgoing_labels),
                        "accepting_suffixes": len(state.accepting_suffixes),
                        "behavior_digest": _digest(state.behavior),
                    }
                    for state in (states[0], witness)
                ],
            }
        )
    return {
        "keys": len(groups),
        "merged_groups": merged,
        "collision_groups": len(collisions),
        "cross_width_collision_groups": cross_width,
        "collisions": collisions,
    }


def _fixed_trace(width: int) -> list[FrontierState]:
    rows = residue_two_affine_pattern(width) if width == 17 else residue_two_explicit_pattern(width)
    state = initial_state(width)
    states = [state]
    for index, row in enumerate(rows):
        state = advance_row(state, row_mask(row))
        if state is None:
            raise ValueError(f"fixed n={width} trace seals a component at row {index}")
        states.append(state)
    return states


def _histogram(values) -> dict[str, int]:
    return {str(value): count for value, count in sorted(Counter(values).items())}


def _source_record(width: int, selection: str, states: list[FrontierState]) -> dict:
    stack_depths = []
    carry_widths = []
    spans = []
    run_keys = set()
    affine_keys = set()
    for state in states:
        word = encode_event_word(width, state.partition)
        if decode_event_word(word) != canonical_rooted_partition(state.partition):
            raise AssertionError("event-word round trip failed")
        metrics = event_metrics(word)
        stack_depths.append(metrics["max_stack_depth"])
        carry_widths.extend(metrics["carry_widths"])
        spans.extend(metrics["component_spans"])
        run_keys.add(motif_key(state, "run_length"))
        affine_keys.add(motif_key(state, "affine"))
    return {
        "width": width,
        "selection": selection,
        "states": len(states),
        "event_word_round_trips": len(states),
        "max_stack_depth_histogram": _histogram(stack_depths),
        "packet_carry_width_histogram": _histogram(carry_widths),
        "component_span_histogram": _histogram(spans),
        "distinct_run_length_motifs": len(run_keys),
        "distinct_affine_motifs": len(affine_keys),
    }


def build_artifact() -> dict:
    corridors = {width: build_equality_corridor(width) for width in CORRIDOR_WIDTHS}
    complete = {
        width: observe_complete_continuations(corridor)
        for width, corridor in corridors.items()
    }
    fixed = {width: _fixed_trace(width) for width in FIXED_WIDTHS}
    sources = {
        f"n{width}-complete-equality-corridor": _source_record(
            width,
            "all unique states in all minimum paths",
            [observation.state for observation in complete[width]],
        )
        for width in CORRIDOR_WIDTHS
    }
    sources.update(
        {
            f"n{width}-fixed-{'near-equality-179-U' if width == 17 else 'equality'}-witness":
            _source_record(width, "one fixed trace", fixed[width])
            for width in FIXED_WIDTHS
        }
    )
    complete_observations = [
        observation for width in CORRIDOR_WIDTHS for observation in complete[width]
    ]
    return {
        "schema": SCHEMA,
        "scope": {
            "semantics": "finite-observed-motif-compression-diagnostic-only",
            "complete_equality_corridors": list(CORRIDOR_WIDTHS),
            "fixed_equality_witnesses": [11, 14],
            "near_equality_control": {"width": 17, "u_count": 179},
            "theorem_or_certificate": False,
            "coverage_beyond_listed_states_claimed": False,
        },
        "definitions": {
            "event_word": "canonical rooted component IDs with per-slot single/open/carry/close interval events, in consecutive packets of at most three face slots",
            "stack_depth": "number of component hull intervals covering a face slot",
            "carry_width": "number of component hull intervals crossing a width-three packet boundary",
            "span": "last minus first frontier occurrence plus one for each represented component",
            "run_length_candidate": "RLE of anonymous packet event/carry symbols, retaining run counts",
            "affine_candidate": "the same RLE with every repeated run count normalized to 2+",
            "continuation_behavior": "complete normalized outgoing equality labels and accepting suffix-label language",
        },
        "sources": sources,
        "coverage": {
            "states": sum(record["states"] for record in sources.values()),
            "lossless_event_word_round_trips": sum(
                record["event_word_round_trips"] for record in sources.values()
            ),
            "complete_continuation_states": len(complete_observations),
            "fixed_trace_states_without_complete_continuation_claim": sum(map(len, fixed.values())),
        },
        "continuation_collisions": {
            candidate: collision_report(complete_observations, candidate)
            for candidate in ("run_length", "affine")
        },
        "limitations": [
            "Collision results use complete continuation behavior only at n=5 and n=8.",
            "The n=11 and n=14 equality witnesses and n=17 control are single fixed traces, not complete corridors.",
            "Anonymous packet motifs deliberately discard component identity and may collide.",
            "No inference at unenumerated widths or for unobserved witnesses is claimed.",
        ],
        "provenance": {
            "producer": "analysis/residue_two_equality_motifs.py",
            "command": [
                "python3", "-B", "analysis/residue_two_equality_motifs.py",
                "--output", "analysis/residue_two_equality_motifs.json",
            ],
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    rendered = json.dumps(build_artifact(), indent=2, sort_keys=True) + "\n"
    if args.check:
        if args.output is None or not args.output.exists() or args.output.read_text() != rendered:
            raise SystemExit(f"stale or missing artifact: {args.output}")
        print(f"finite motif diagnostic matches {args.output}")
    else:
        if args.output is not None:
            args.output.write_text(rendered)
        print(rendered, end="")


if __name__ == "__main__":
    main()
