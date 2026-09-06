#!/usr/bin/env python3
"""Exact forward and bidirectional moving-seam search for n=14 to n=17.

Rows are generated packet by packet through :func:`stream_row_packets`.  The
default language freezes affine rows 0..2 and 15..16 and otherwise applies the
strict-boundary radius tube around one smoothly moving inserted packet.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import tempfile
import time
from bisect import bisect_right
from collections import defaultdict
from dataclasses import asdict, dataclass, field
from itertools import product
from pathlib import Path
from typing import Sequence

from analysis.patterns.construction_lab import (
    dual_connectivity_check,
    forest_completion_check,
    run_check,
)
from analysis.patterns.construction_lab import (
    q_old_formula as q_formula,
)
from analysis.patterns.diagonal_patterns import (
    residue_two_affine_pattern,
    residue_two_pattern,
)
from analysis.tiles.tile_grammar import (
    FrontierState,
    initial_state,
    merge_frontier_profile,
    render_mask,
    stream_row_packets,
)
from analysis.transport.census_moving_seam_alignment import (
    find_alignment,
    replay_alignment,
)

PACKET_ALPHABET = {
    "".join(bits): "".join("U" if bit == "1" else "." for bit in bits)
    for bits in product("01", repeat=3)
}
PACKET_NAME = {value: name for name, value in PACKET_ALPHABET.items()}
ALL_PACKETS = tuple(PACKET_ALPHABET)
DEFAULT_FIXED_ROWS = (0, 1, 2, 15, 16)
SCHEMA = "grid-graphs.residue-two-moving-seam-search.v2"


@dataclass(frozen=True, slots=True)
class PathStep:
    target_row: int
    operation: str
    source_row: int
    source_cursor_before: int
    seam: int


@dataclass(frozen=True, slots=True, order=True)
class AlignmentState:
    cursor: int
    holds: int
    previous_seam: int
    baseline_hold_removals: int = 0
    baseline_advance_insertions: int = 0


@dataclass(frozen=True, slots=True)
class AlignmentTransition:
    target_row: int
    before: AlignmentState
    after: AlignmentState
    operation: str
    source_row: int
    seam: int


@dataclass(frozen=True, slots=True)
class AlignmentAutomaton:
    layers: tuple[tuple[AlignmentState, ...], ...]
    forward: tuple[tuple[AlignmentTransition, ...], ...]
    reverse: tuple[tuple[AlignmentTransition, ...], ...]


@dataclass(frozen=True, slots=True)
class ScheduleTemplate:
    """Fixed geometry usable with any tube at least ``minimum_radius``."""

    name: str
    source_n: int
    target_n: int
    minimum_radius: int
    transitions: tuple[AlignmentTransition, ...]


@dataclass(frozen=True, slots=True)
class CompatibleSchedule:
    """All complete fixed-target schedules calibrated at one exact radius."""

    name: str
    calibration_radius: int
    automaton: AlignmentAutomaton
    complete_path_count: int
    metadata: dict[str, object] = field(default_factory=dict)

    @property
    def layer_state_counts(self) -> tuple[int, ...]:
        return tuple(len(layer) for layer in self.automaton.layers)

    @property
    def layer_edge_counts(self) -> tuple[int, ...]:
        return tuple(len(edges) for edges in self.automaton.forward)


@dataclass(slots=True)
class Node:
    state: FrontierState
    alignment: AlignmentState
    parent: Node | None
    row_mask: int | None
    transition: AlignmentTransition | None
    boundary_rewrites: int = 0


@dataclass(frozen=True, slots=True)
class RowStats:
    row: int
    incoming_states: int
    attempted_packet_extensions: int
    generated_row_transitions: int
    deduplicated_states: int
    cost_prunes: int
    rank_prunes: int


@dataclass(frozen=True, slots=True)
class SearchResult:
    schema: str
    source_n: int
    target_n: int
    radius: int
    u_count: int
    fixed_rows: tuple[int, ...]
    target_fully_fixed: bool
    schedule: str | None
    conclusion: str
    complete: bool
    elapsed_seconds: float
    final_states: int
    witness: tuple[str, ...] | None
    steps: tuple[PathStep, ...] | None
    validation: dict | None
    stats: tuple[RowStats, ...]
    boundary_rewrites: int = 0


@dataclass(frozen=True, slots=True)
class SideRowStats:
    side: str
    target_row: int
    depth: int
    incoming_states: int
    alignment_transitions: int
    attempted_packet_extensions: int
    generated_row_transitions: int
    deduplicated_states: int
    cost_prunes: int
    rank_prunes: int


@dataclass(frozen=True, slots=True)
class JoinStats:
    alignment_buckets: int
    candidate_state_pairs: int
    cost_pruned_pairs: int
    merged_pairs: int
    connected_pairs: int
    cache_hits: int = 0
    merge_evaluations: int = 0
    scope_pruned_pairs: int = 0


@dataclass(slots=True)
class BidirectionalFrontiers:
    source: tuple[str, ...]
    target_n: int
    radius: int
    u_limit: int
    cut: int
    fixed_rows: tuple[int, ...]
    fixed_target: tuple[str, ...] | None
    schedule: str | None
    top: list[Node]
    bottom: list[Node]
    top_stats: tuple[SideRowStats, ...]
    bottom_stats: tuple[SideRowStats, ...]
    elapsed_seconds: float
    boundary_rewrites: int = 0
    connectivity_cache: dict[tuple[tuple[int, ...], tuple[int, ...], int], bool] = (
        field(default_factory=dict)
    )


@dataclass(frozen=True, slots=True)
class BidirectionalResult:
    schema: str
    source_n: int
    target_n: int
    radius: int
    u_count: int
    cut: int
    fixed_rows: tuple[int, ...]
    target_fully_fixed: bool
    schedule: str | None
    conclusion: str
    complete: bool
    elapsed_seconds: float
    top_states: int
    bottom_states: int
    witness: tuple[str, ...] | None
    steps: tuple[PathStep, ...] | None
    validation: dict | None
    top_stats: tuple[SideRowStats, ...]
    bottom_stats: tuple[SideRowStats, ...]
    join_stats: JoinStats
    boundary_rewrites: int = 0


def _packets(row: str) -> tuple[str, ...]:
    if (len(row) - 2) % 3:
        raise ValueError("row width must be 3k+2")
    return tuple(row[start : start + 3] for start in range(1, len(row) - 1, 3))


def row_packet_domains(
    source_row: str,
    seam: int,
    radius: int,
    fixed_row: str | None = None,
) -> tuple[str, str, tuple[tuple[str, ...], ...]] | None:
    """Return the exact streamed domain for one source-row/seam comparison."""
    source_packets = _packets(source_row)
    target_packet_count = len(source_packets) + 1
    if seam not in range(target_packet_count) or radius < 0:
        raise ValueError("invalid seam or radius")
    if fixed_row is not None and len(fixed_row) != len(source_row) + 3:
        raise ValueError("fixed row has the wrong width")

    prefix, suffix = source_row[0], source_row[-1]
    fixed_packets = _packets(fixed_row) if fixed_row is not None else None
    if fixed_row is not None and (fixed_row[0] != prefix or fixed_row[-1] != suffix):
        return None
    domains = []
    for target_packet in range(target_packet_count):
        if target_packet == seam or abs(target_packet - seam) <= radius:
            domain: tuple[str, ...] = ALL_PACKETS
        else:
            source_packet = target_packet if target_packet < seam else target_packet - 1
            domain = (PACKET_NAME[source_packets[source_packet]],)
        if fixed_packets is not None:
            fixed_name = PACKET_NAME[fixed_packets[target_packet]]
            if fixed_name not in domain:
                return None
            domain = (fixed_name,)
        domains.append(domain)
    return prefix, suffix, tuple(domains)


def row_boundary_variants(
    source_row: str,
    fixed_row: str | None = None,
    boundary_rewrites: int = 0,
) -> tuple[tuple[str, str, int], ...]:
    """Return exact (left, right, rewrite count) boundary choices for one row."""
    if boundary_rewrites not in (0, 1):
        raise ValueError("boundary_rewrites must be zero or one")
    if fixed_row is not None:
        if len(fixed_row) != len(source_row) + 3:
            raise ValueError("fixed row has the wrong width")
        delta = (fixed_row[0] != source_row[0]) + (fixed_row[-1] != source_row[-1])
        return (
            ((fixed_row[0], fixed_row[-1], delta),)
            if delta <= boundary_rewrites
            else ()
        )

    left, right = source_row[0], source_row[-1]
    variants = [(left, right, 0)]
    if boundary_rewrites:
        toggle = {".": "U", "U": "."}
        variants.extend(((toggle[left], right, 1), (left, toggle[right], 1)))
    return tuple(dict.fromkeys(variants))


def row_domain_variants(
    source_row: str,
    seam: int,
    radius: int,
    fixed_row: str | None = None,
    boundary_rewrites: int = 0,
) -> tuple[tuple[str, str, tuple[tuple[str, ...], ...], int], ...]:
    """Return packet domains paired with every allowed boundary rewrite lane."""
    boundaries = row_boundary_variants(source_row, fixed_row, boundary_rewrites)
    if not boundaries:
        return ()
    constrained = fixed_row
    if fixed_row is not None:
        constrained = source_row[0] + fixed_row[1:-1] + source_row[-1]
    specification = row_packet_domains(source_row, seam, radius, constrained)
    if specification is None:
        return ()
    _, _, domains = specification
    return tuple((*boundary, domains, delta) for *boundary, delta in boundaries)


def enumerate_domain_rows(
    source_row: str,
    seam: int,
    radius: int,
    fixed_row: str | None = None,
    boundary_rewrites: int = 0,
) -> set[str]:
    """Materialize a row domain for tests and language diagnostics only."""
    return {
        prefix + "".join(PACKET_ALPHABET[name] for name in names) + suffix
        for prefix, suffix, domains, _ in row_domain_variants(
            source_row, seam, radius, fixed_row, boundary_rewrites
        )
        for names in product(*domains)
    }


def exact_state_key(node: Node) -> tuple:
    """Future behavior key; row index is implicit in the search layer.

    For equal keys, lower U cost dominates because all future costs are
    nonnegative and acceptance is an upper bound.  ``cycle_excess`` is omitted
    because row advancement and final validation never branch on it; the full
    representative state is nevertheless retained for the next transition.
    """
    return (
        node.alignment,
        node.state.previous_u_mask,
        node.state.partition,
        node.boundary_rewrites,
    )


def _transition_kinds(
    cursor: int, source_size: int
) -> tuple[tuple[str, int, int], ...]:
    choices = []
    if cursor < source_size:
        choices.append(("ADVANCE", cursor, cursor + 1))
    if cursor > 0:
        choices.append(("HOLD", cursor - 1, cursor))
    return tuple(choices)


def build_alignment_automaton(
    source_n: int = 14, target_n: int = 17, seams: int = 5
) -> AlignmentAutomaton:
    """Build all reachable exact alignment edges and their literal reversal."""
    if target_n != source_n + 3 or seams < 1:
        raise ValueError("alignment requires target_n=source_n+3 and at least one seam")
    layers: list[set[AlignmentState]] = [{AlignmentState(0, 0, -1)}]
    forward: list[tuple[AlignmentTransition, ...]] = []
    for target_row in range(target_n):
        edges = []
        children = set()
        for before in sorted(layers[-1]):
            for operation, source_row, next_cursor in _transition_kinds(
                before.cursor, source_n
            ):
                next_holds = before.holds + (operation == "HOLD")
                if next_holds > 3:
                    continue
                current_seams = (
                    range(seams)
                    if before.previous_seam < 0
                    else range(
                        max(0, before.previous_seam - 1),
                        min(seams, before.previous_seam + 2),
                    )
                )
                for seam in current_seams:
                    after = AlignmentState(next_cursor, next_holds, seam)
                    edge = AlignmentTransition(
                        target_row, before, after, operation, source_row, seam
                    )
                    edges.append(edge)
                    children.add(after)
        forward.append(tuple(edges))
        layers.append(children)

    finals = {AlignmentState(source_n, 3, seam) for seam in range(seams)}
    if layers[-1] != finals:
        raise AssertionError("alignment automaton has unexpected final layer")
    reverse: list[tuple[AlignmentTransition, ...]] = [() for _ in range(target_n)]
    reachable = finals
    for row in range(target_n - 1, -1, -1):
        reversed_edges = tuple(edge for edge in forward[row] if edge.after in reachable)
        reverse[row] = reversed_edges
        reachable = {edge.before for edge in reversed_edges}
    if reachable != layers[0]:
        raise AssertionError("alignment automaton contains a non-completable prefix")
    return AlignmentAutomaton(
        tuple(tuple(sorted(layer)) for layer in layers),
        tuple(forward),
        tuple(reverse),
    )


def affine_schedule_template(source: Sequence[str] | None = None) -> ScheduleTemplate:
    """Derive radius-one geometry once; wider radii only widen row domains."""
    source = tuple(source or residue_two_pattern(14))
    target = tuple(residue_two_affine_pattern(17))
    alignment = find_alignment(source, target, 1, allow_boundary_rewrites=False)
    if alignment is None:
        raise AssertionError("affine-17 has no strict radius-one alignment")
    replay_alignment(source, target, alignment)
    transitions = []
    cursor = holds = 0
    previous_seam = -1
    for step in alignment.steps:
        before = AlignmentState(cursor, holds, previous_seam)
        cursor += step.operation == "ADVANCE"
        holds += step.operation == "HOLD"
        after = AlignmentState(cursor, holds, step.seam)
        edge = AlignmentTransition(
            step.target_row,
            before,
            after,
            step.operation,
            step.source_row,
            step.seam,
        )
        if step.source_cursor_before != before.cursor:
            raise AssertionError("census template cursor disagrees with replay")
        transitions.append(edge)
        previous_seam = step.seam
    if (cursor, holds) != (len(source), 3):
        raise AssertionError("affine template is not a complete alignment")
    return ScheduleTemplate("affine", len(source), len(target), 1, tuple(transitions))


def schedule_automaton(template: ScheduleTemplate) -> AlignmentAutomaton:
    """Encode a fixed schedule as a one-edge-per-row alignment automaton."""
    if len(template.transitions) != template.target_n:
        raise ValueError("schedule does not span the target height")
    layers = [(template.transitions[0].before,)]
    for row, edge in enumerate(template.transitions):
        if edge.target_row != row or edge.before != layers[-1][0]:
            raise ValueError("schedule transitions are not a contiguous path")
        layers.append((edge.after,))
    forward = tuple((edge,) for edge in template.transitions)
    return AlignmentAutomaton(tuple(layers), forward, forward)


def compatible_schedule_automaton(
    base: AlignmentAutomaton,
    source: Sequence[str],
    target: Sequence[str],
    radius: int,
    *,
    name: str = "compatible",
    metadata: dict[str, object] | None = None,
    boundary_rewrites: int = 0,
) -> CompatibleSchedule:
    """Retain exactly edges lying on complete fixed-target alignment paths."""
    if len(target) != len(base.forward) or radius < 0:
        raise ValueError("target height or compatibility radius is invalid")
    eligible = []
    for row, edges in enumerate(base.forward):
        eligible.append(
            tuple(
                edge
                for edge in edges
                if row_domain_variants(
                    source[edge.source_row],
                    edge.seam,
                    radius,
                    target[row],
                    boundary_rewrites,
                )
            )
        )

    forward_states = [{base.layers[0][0]}]
    for edges in eligible:
        forward_states.append(
            {edge.after for edge in edges if edge.before in forward_states[-1]}
        )
    backward_states: list[set[AlignmentState]] = [set() for _ in base.layers]
    backward_states[-1] = set(base.layers[-1]) & forward_states[-1]
    retained: list[tuple[AlignmentTransition, ...]] = [() for _ in eligible]
    for row in range(len(eligible) - 1, -1, -1):
        retained[row] = tuple(
            edge
            for edge in eligible[row]
            if edge.before in forward_states[row]
            and edge.after in backward_states[row + 1]
        )
        backward_states[row] = {edge.before for edge in retained[row]}
    layers = tuple(
        tuple(sorted(forward_states[row] & backward_states[row]))
        for row in range(len(base.layers))
    )

    path_counts = {base.layers[0][0]: 1}
    for edges in retained:
        following: dict[AlignmentState, int] = defaultdict(int)
        for edge in edges:
            following[edge.after] += path_counts.get(edge.before, 0)
        path_counts = following
    complete_paths = sum(path_counts.values())
    automaton = AlignmentAutomaton(layers, tuple(retained), tuple(retained))
    return CompatibleSchedule(name, radius, automaton, complete_paths, metadata or {})


def complete_operation_words(
    schedule: CompatibleSchedule,
) -> tuple[tuple[str, ...], ...]:
    """Return all complete operation words in deterministic lexicographic order."""
    words_by_state: dict[AlignmentState, set[tuple[str, ...]]] = {
        state: {()} for state in schedule.automaton.layers[0]
    }
    for edges in schedule.automaton.forward:
        following: dict[AlignmentState, set[tuple[str, ...]]] = defaultdict(set)
        for edge in edges:
            following[edge.after].update(
                (*word, edge.operation)
                for word in words_by_state.get(edge.before, ())
            )
        words_by_state = following
    return tuple(sorted({word for words in words_by_state.values() for word in words}))


def operation_word_hash(operation_word: Sequence[str]) -> str:
    """Return the reproducible SHA-256 identifier used by schedule artifacts."""
    encoded = json.dumps(list(operation_word), separators=(",", ":")).encode()
    return hashlib.sha256(encoded).hexdigest()


def compatible_schedule_for_operation_word(
    schedule: CompatibleSchedule,
    operation_word: Sequence[str],
    *,
    index: int | None = None,
) -> CompatibleSchedule:
    """Project a compatible automaton onto one complete operation word.

    Edges are first intersected with the requested row label and are then
    trimmed by forward and backward reachability. Thus no dead edge survives.
    """
    word = tuple(operation_word)
    automaton = schedule.automaton
    if len(word) != len(automaton.forward):
        raise ValueError("operation word has the wrong length")

    eligible = tuple(
        tuple(edge for edge in edges if edge.operation == word[row])
        for row, edges in enumerate(automaton.forward)
    )
    reachable: list[set[AlignmentState]] = [set(automaton.layers[0])]
    for edges in eligible:
        reachable.append(
            {edge.after for edge in edges if edge.before in reachable[-1]}
        )
    completable: list[set[AlignmentState]] = [set() for _ in automaton.layers]
    completable[-1] = reachable[-1] & set(automaton.layers[-1])
    retained: list[tuple[AlignmentTransition, ...]] = [() for _ in eligible]
    for row in range(len(eligible) - 1, -1, -1):
        retained[row] = tuple(
            edge
            for edge in eligible[row]
            if edge.before in reachable[row]
            and edge.after in completable[row + 1]
        )
        completable[row] = {edge.before for edge in retained[row]}
    if not completable[0]:
        raise ValueError("operation word is not accepted by the schedule")

    layers = tuple(
        tuple(sorted(reachable[row] & completable[row]))
        for row in range(len(automaton.layers))
    )
    path_counts = {state: 1 for state in layers[0]}
    for edges in retained:
        following: dict[AlignmentState, int] = defaultdict(int)
        for edge in edges:
            following[edge.after] += path_counts.get(edge.before, 0)
        path_counts = following
    path_count = sum(path_counts.values())
    metadata = dict(schedule.metadata)
    metadata.update(
        {
            "parent_schedule": schedule.name,
            "operation_word": list(word),
            "operation_word_hash": operation_word_hash(word),
            "fixed_target_has_representation": path_count > 0,
        }
    )
    if index is not None:
        metadata["operation_word_index"] = index
    projected = AlignmentAutomaton(layers, tuple(retained), tuple(retained))
    suffix = f"-{index:02d}" if index is not None else ""
    return CompatibleSchedule(
        f"{schedule.name}-word{suffix}",
        schedule.calibration_radius,
        projected,
        path_count,
        metadata,
    )


def compatible_schedule_operation_word_shards(
    schedule: CompatibleSchedule,
) -> tuple[CompatibleSchedule, ...]:
    """Return one deterministic, disjoint compatible shard per complete word."""
    return tuple(
        compatible_schedule_for_operation_word(schedule, word, index=index)
        for index, word in enumerate(complete_operation_words(schedule))
    )


def affine_compatible_schedule(
    source: Sequence[str] | None = None,
) -> CompatibleSchedule:
    """Return all strict affine-17 schedules calibrated at radius one."""
    source = tuple(source or residue_two_pattern(14))
    target = tuple(residue_two_affine_pattern(17))
    base = build_alignment_automaton(len(source), len(target), (len(target) - 2) // 3)
    return compatible_schedule_automaton(
        base, source, target, 1, name="affine-compatible"
    )


def holds_compatible_schedule_automaton(
    template: ScheduleTemplate,
    source: Sequence[str],
    target: Sequence[str],
    radius: int,
    *,
    seams: int,
    name: str = "holds-compatible",
) -> CompatibleSchedule:
    """Freeze operation/cursor evolution while retaining all viable seam paths."""
    if seams < 1 or len(template.transitions) != len(target):
        raise ValueError("invalid seam count or target height")
    layers: list[set[AlignmentState]] = [{template.transitions[0].before}]
    forward = []
    for row, fixed in enumerate(template.transitions):
        edges = []
        following = set()
        for before in sorted(layers[-1]):
            if (before.cursor, before.holds) != (
                fixed.before.cursor,
                fixed.before.holds,
            ):
                raise ValueError("template cursor/holds evolution is inconsistent")
            choices = (
                range(seams)
                if before.previous_seam < 0
                else range(
                    max(0, before.previous_seam - 1),
                    min(seams, before.previous_seam + 2),
                )
            )
            for seam in choices:
                after = AlignmentState(fixed.after.cursor, fixed.after.holds, seam)
                edges.append(
                    AlignmentTransition(
                        row,
                        before,
                        after,
                        fixed.operation,
                        fixed.source_row,
                        seam,
                    )
                )
                following.add(after)
        forward.append(tuple(edges))
        layers.append(following)
    raw = AlignmentAutomaton(
        tuple(tuple(sorted(layer)) for layer in layers),
        tuple(forward),
        tuple(forward),
    )
    return compatible_schedule_automaton(raw, source, target, radius, name=name)


def affine_holds_compatible_schedule(
    source: Sequence[str] | None = None,
) -> CompatibleSchedule:
    """Return radius-one affine-compatible seams on fixed affine HOLD geometry."""
    source = tuple(source or residue_two_pattern(14))
    target = tuple(residue_two_affine_pattern(17))
    template = affine_schedule_template(source)
    return holds_compatible_schedule_automaton(
        template,
        source,
        target,
        1,
        seams=5,
        name="affine-holds-compatible",
    )


def one_hold_relocation_schedule_automaton(
    template: ScheduleTemplate,
    source: Sequence[str],
    target: Sequence[str],
    radius: int,
    *,
    seams: int,
    relocation_count: int = 1,
    name: str = "one-hold-relocation",
) -> CompatibleSchedule:
    """Relocate exactly ``relocation_count`` baseline HOLDs on complete paths."""
    if (
        seams < 1
        or not 0 <= relocation_count <= 3
        or template.source_n != len(source)
        or template.target_n != len(target)
        or len(template.transitions) != len(target)
    ):
        raise ValueError("invalid seam count or target height")
    schedule_automaton(template)
    baseline_operations = tuple(edge.operation for edge in template.transitions)
    if (
        baseline_operations.count("ADVANCE") != len(source)
        or baseline_operations.count("HOLD") != 3
    ):
        raise ValueError("baseline must contain source_n ADVANCEs and three HOLDs")
    initial = AlignmentState(0, 0, -1)
    layers: list[set[AlignmentState]] = [{initial}]
    forward = []
    for row, baseline in enumerate(template.transitions):
        edges = []
        following = set()
        for before in sorted(layers[-1]):
            operations = [(baseline.operation, 0, 0)]
            if (
                baseline.operation == "HOLD"
                and before.baseline_hold_removals < relocation_count
            ):
                operations.append(("ADVANCE", 1, 0))
            elif (
                baseline.operation == "ADVANCE"
                and before.baseline_advance_insertions < relocation_count
            ):
                operations.append(("HOLD", 0, 1))
            seam_choices = (
                range(seams)
                if before.previous_seam < 0
                else range(
                    max(0, before.previous_seam - 1),
                    min(seams, before.previous_seam + 2),
                )
            )
            for operation, removed, inserted in operations:
                choice = next(
                    (
                        item
                        for item in _transition_kinds(before.cursor, len(source))
                        if item[0] == operation
                    ),
                    None,
                )
                if choice is None:
                    continue
                _, source_row, next_cursor = choice
                for seam in seam_choices:
                    after = AlignmentState(
                        next_cursor,
                        before.holds + (operation == "HOLD"),
                        seam,
                        before.baseline_hold_removals + removed,
                        before.baseline_advance_insertions + inserted,
                    )
                    edges.append(
                        AlignmentTransition(
                            row, before, after, operation, source_row, seam
                        )
                    )
                    following.add(after)
        forward.append(tuple(edges))
        layers.append(following)

    finals = {
        state
        for state in layers[-1]
        if (
            state.cursor,
            state.holds,
            state.baseline_hold_removals,
            state.baseline_advance_insertions,
        )
        == (len(source), 3, relocation_count, relocation_count)
    }
    completable = finals
    retained: list[tuple[AlignmentTransition, ...]] = [() for _ in forward]
    for row in range(len(forward) - 1, -1, -1):
        retained[row] = tuple(
            edge for edge in forward[row] if edge.after in completable
        )
        completable = {edge.before for edge in retained[row]}
    if completable != {initial}:
        raise AssertionError(
            "exact relocation automaton has no complete operation word"
        )
    raw_layers = tuple(
        tuple(
            sorted(
                {initial} if row == 0 else {edge.after for edge in retained[row - 1]}
            )
        )
        for row in range(len(layers))
    )
    raw = AlignmentAutomaton(raw_layers, tuple(retained), tuple(retained))
    count_name = {0: "zero", 1: "one", 2: "two", 3: "three"}[relocation_count]
    metadata: dict[str, object] = {
        "scope": f"exactly-{count_name}-hold-relocation"
        + ("s" if relocation_count != 1 else ""),
        "baseline_schedule": template.name,
        "baseline_operation_word": list(baseline_operations),
        "baseline_hold_rows": [
            row
            for row, operation in enumerate(baseline_operations)
            if operation == "HOLD"
        ],
        "baseline_advance_rows": [
            row
            for row, operation in enumerate(baseline_operations)
            if operation == "ADVANCE"
        ],
        "required_baseline_hold_removals": relocation_count,
        "required_baseline_advance_insertions": relocation_count,
        "strict_boundary": True,
        "seam_range": [0, seams - 1],
        "maximum_seam_step": 1,
    }
    schedule = compatible_schedule_automaton(
        raw, source, target, radius, name=name, metadata=metadata
    )
    words_by_state: dict[AlignmentState, set[tuple[str, ...]]] = {initial: {()}}
    for edges in schedule.automaton.forward:
        following: dict[AlignmentState, set[tuple[str, ...]]] = defaultdict(set)
        for edge in edges:
            following[edge.after].update(
                (*word, edge.operation) for word in words_by_state.get(edge.before, ())
            )
        words_by_state = following
    schedule.metadata["complete_operation_word_count"] = len(
        {word for words in words_by_state.values() for word in words}
    )
    return schedule


def affine_one_hold_relocation_schedule(
    source: Sequence[str] | None = None,
) -> CompatibleSchedule:
    """Return exact one-HOLD relocations compatible with fixed affine-17 rows."""
    source = tuple(source or residue_two_pattern(14))
    target = tuple(residue_two_affine_pattern(17))
    schedule = one_hold_relocation_schedule_automaton(
        affine_schedule_template(source),
        source,
        target,
        1,
        seams=5,
        name="affine-one-hold-relocation",
    )
    schedule.metadata["compatibility_target"] = "residue_two_affine_pattern(17)"
    schedule.metadata["fixed_target_has_representation"] = (
        schedule.complete_path_count > 0
    )
    return schedule


def affine_two_hold_relocation_schedule(
    source: Sequence[str] | None = None,
) -> CompatibleSchedule:
    """Return exact two-HOLD relocations compatible with fixed affine-17 rows."""
    source = tuple(source or residue_two_pattern(14))
    target = tuple(residue_two_affine_pattern(17))
    schedule = one_hold_relocation_schedule_automaton(
        affine_schedule_template(source),
        source,
        target,
        1,
        seams=5,
        relocation_count=2,
        name="affine-two-hold-relocation",
    )
    schedule.metadata["compatibility_target"] = "residue_two_affine_pattern(17)"
    schedule.metadata["fixed_target_has_representation"] = (
        schedule.complete_path_count > 0
    )
    return schedule


def _resolve_schedule(
    schedule: str | ScheduleTemplate | CompatibleSchedule | None,
    source: Sequence[str],
    target_n: int,
    radius: int,
) -> tuple[ScheduleTemplate | CompatibleSchedule | None, AlignmentAutomaton]:
    if schedule == "affine":
        schedule = affine_schedule_template(source)
    elif schedule == "affine-compatible":
        schedule = affine_compatible_schedule(source)
    elif schedule == "affine-holds-compatible":
        schedule = affine_holds_compatible_schedule(source)
    elif schedule == "affine-one-hold-relocation":
        schedule = affine_one_hold_relocation_schedule(source)
    elif schedule == "affine-two-hold-relocation":
        schedule = affine_two_hold_relocation_schedule(source)
    elif isinstance(schedule, str):
        raise ValueError(f"unknown schedule template: {schedule}")
    if schedule is None:
        return None, build_alignment_automaton(
            len(source), target_n, (target_n - 2) // 3
        )
    if isinstance(schedule, CompatibleSchedule):
        if radius != schedule.calibration_radius:
            raise ValueError("compatible schedule is calibrated exactly at radius one")
        return schedule, schedule.automaton
    if (
        schedule.source_n != len(source)
        or schedule.target_n != target_n
        or radius < schedule.minimum_radius
    ):
        raise ValueError(
            "schedule dimensions do not match or radius is below its minimum"
        )
    return schedule, schedule_automaton(schedule)


def schedule_accepts_steps(
    template: ScheduleTemplate, steps: Sequence[PathStep]
) -> bool:
    """Return whether operation/source/cursor/seam exactly match the template."""
    if len(steps) != len(template.transitions):
        return False
    return all(
        (
            step.target_row,
            step.operation,
            step.source_row,
            step.source_cursor_before,
            step.seam,
        )
        == (
            edge.target_row,
            edge.operation,
            edge.source_row,
            edge.before.cursor,
            edge.seam,
        )
        for step, edge in zip(steps, template.transitions, strict=True)
    )


def _path(
    node: Node, *, reverse: bool = False
) -> tuple[tuple[int, ...], tuple[AlignmentTransition, ...]]:
    masks = []
    transitions = []
    current = node
    while current.parent is not None:
        assert current.row_mask is not None and current.transition is not None
        masks.append(current.row_mask)
        transitions.append(current.transition)
        current = current.parent
    if not reverse:
        masks.reverse()
        transitions.reverse()
    return tuple(masks), tuple(transitions)


def _steps(transitions: Sequence[AlignmentTransition]) -> tuple[PathStep, ...]:
    return tuple(
        PathStep(
            edge.target_row,
            edge.operation,
            edge.source_row,
            edge.before.cursor,
            edge.seam,
        )
        for edge in transitions
    )


def _rank_deficit_impossible(state: FrontierState, budget: int) -> bool:
    introduced = 1 + min(state.row_index, state.n - 1) * (state.n - 1)
    current_rank = introduced - len(set(state.partition))
    required_rank = (state.n - 1) ** 2
    return current_rank + 2 * (budget - state.u_cost) < required_rank


def _validate_witness(rows: tuple[str, ...], u_limit: int) -> dict:
    materialized = list(rows)
    dual_ok, connected, total = dual_connectivity_check(materialized)
    forest_ok, forest_reason = forest_completion_check(materialized)
    u_count = sum(row.count("U") for row in rows)
    validation = {
        "u_count": u_count,
        "within_u_limit": u_count <= u_limit,
        "dual_ok": dual_ok,
        "dual_connected": connected,
        "dual_total": total,
        "forest_ok": forest_ok,
        "forest_reason": forest_reason,
    }
    if u_count == q_formula(len(rows)):
        validation["run_check"] = run_check(len(rows), materialized)
    validation["accepted"] = validation["within_u_limit"] and dual_ok and forest_ok
    return validation


def replay_path(
    source: Sequence[str],
    rows: Sequence[str],
    steps: Sequence[PathStep],
    radius: int,
    boundary_rewrites: int = 0,
) -> int:
    """Independently replay transducer operations and row-domain membership."""
    cursor = holds = 0
    observed_boundary_rewrites = 0
    previous_seam = None
    if len(rows) != len(steps):
        raise ValueError("path does not emit every row")
    for target_row, (row, step) in enumerate(zip(rows, steps, strict=True)):
        if step.target_row != target_row or step.source_cursor_before != cursor:
            raise ValueError("path row or cursor is inconsistent")
        choice = next(
            (
                item
                for item in _transition_kinds(cursor, len(source))
                if item[:2] == (step.operation, step.source_row)
            ),
            None,
        )
        if choice is None:
            raise ValueError("path operation is unavailable")
        if previous_seam is not None and abs(step.seam - previous_seam) > 1:
            raise ValueError("seam moves by more than one")
        source_row = source[step.source_row]
        observed_boundary_rewrites += (row[0] != source_row[0]) + (
            row[-1] != source_row[-1]
        )
        if observed_boundary_rewrites > boundary_rewrites:
            raise ValueError("path exceeds its boundary rewrite budget")
        normalized = source_row[0] + row[1:-1] + source_row[-1]
        if normalized not in enumerate_domain_rows(source_row, step.seam, radius):
            raise ValueError("row is outside its moving-seam domain")
        cursor = choice[2]
        holds += step.operation == "HOLD"
        previous_seam = step.seam
    if cursor != len(source) or holds != 3:
        raise ValueError("path does not consume source with exactly three HOLDs")
    return observed_boundary_rewrites


def language_membership(
    target: Sequence[str],
    *,
    source: Sequence[str] | None = None,
    radius: int = 1,
    fixed_rows: Sequence[int] = DEFAULT_FIXED_ROWS,
    boundary_rewrites: int = 0,
) -> bool:
    """Check strict-boundary transducer membership, including fixed caps."""
    source = tuple(source or residue_two_pattern(14))
    target = tuple(target)
    if any(
        target[row] != residue_two_affine_pattern(len(target))[row]
        for row in fixed_rows
    ):
        return False
    if boundary_rewrites not in (0, 1):
        raise ValueError("boundary_rewrites must be zero or one")
    automaton = build_alignment_automaton(
        len(source), len(target), (len(target) - 2) // 3
    )
    states = {(automaton.layers[0][0], 0)}
    for row, edges in enumerate(automaton.forward):
        following = set()
        for edge in edges:
            for state, used in states:
                if edge.before != state:
                    continue
                source_row = source[edge.source_row]
                delta = (target[row][0] != source_row[0]) + (
                    target[row][-1] != source_row[-1]
                )
                if used + delta > boundary_rewrites:
                    continue
                normalized = source_row[0] + target[row][1:-1] + source_row[-1]
                if normalized in enumerate_domain_rows(source_row, edge.seam, radius):
                    following.add((edge.after, used + delta))
        states = following
        if not states:
            return False
    return any(state in automaton.layers[-1] for state, _ in states)


def _fixed_row(
    row: int,
    affine: Sequence[str] | None,
    fixed_rows: set[int],
    fixed_target: Sequence[str] | None,
) -> str | None:
    if fixed_target is not None:
        return fixed_target[row]
    return affine[row] if row in fixed_rows and affine is not None else None


def _edge_row_minimum(
    source: Sequence[str],
    edge: AlignmentTransition,
    radius: int,
    constrained: str | None,
    boundary_rewrites: int = 0,
) -> int | None:
    variants = row_domain_variants(
        source[edge.source_row],
        edge.seam,
        radius,
        constrained,
        boundary_rewrites,
    )
    if not variants:
        return None
    return min(
        prefix.count("U")
        + suffix.count("U")
        + sum(
            min(PACKET_ALPHABET[name].count("U") for name in domain)
            for domain in domains
        )
        for prefix, suffix, domains, _ in variants
    )


def alignment_cost_bounds(
    automaton: AlignmentAutomaton,
    source: Sequence[str],
    radius: int,
    affine: Sequence[str] | None,
    fixed_rows: set[int],
    fixed_target: Sequence[str] | None,
    boundary_rewrites: int = 0,
) -> tuple[
    tuple[dict[AlignmentState, int], ...], tuple[dict[AlignmentState, int], ...]
]:
    """Return exact minimum prefix/suffix row costs, ignoring topology."""
    target_n = len(automaton.forward)
    prefix: list[dict[AlignmentState, int]] = [{automaton.layers[0][0]: 0}]
    edge_costs: dict[AlignmentTransition, int] = {}
    for row, edges in enumerate(automaton.forward):
        constrained = _fixed_row(row, affine, fixed_rows, fixed_target)
        following: dict[AlignmentState, int] = {}
        for edge in edges:
            cost = _edge_row_minimum(
                source, edge, radius, constrained, boundary_rewrites
            )
            if cost is None:
                continue
            edge_costs[edge] = cost
            if edge.before not in prefix[-1]:
                continue
            value = prefix[-1][edge.before] + cost
            following[edge.after] = min(following.get(edge.after, value), value)
        prefix.append(following)

    suffix: list[dict[AlignmentState, int]] = [{} for _ in range(target_n + 1)]
    suffix[target_n] = {state: 0 for state in automaton.layers[target_n]}
    for row in range(target_n - 1, -1, -1):
        current: dict[AlignmentState, int] = {}
        for edge in automaton.reverse[row]:
            if edge not in edge_costs or edge.after not in suffix[row + 1]:
                continue
            value = edge_costs[edge] + suffix[row + 1][edge.after]
            current[edge.before] = min(current.get(edge.before, value), value)
        suffix[row] = current
    return tuple(prefix), tuple(suffix)


def _expand_side(
    *,
    side: str,
    source: Sequence[str],
    target_n: int,
    radius: int,
    u_count: int,
    cut: int,
    automaton: AlignmentAutomaton,
    prefix_cost: Sequence[dict[AlignmentState, int]],
    suffix_cost: Sequence[dict[AlignmentState, int]],
    affine: Sequence[str] | None,
    fixed_rows: set[int],
    fixed_target: Sequence[str] | None,
    boundary_rewrites: int,
    report: bool,
) -> tuple[list[Node], tuple[SideRowStats, ...]]:
    if side == "top":
        layer = [
            Node(initial_state(target_n), automaton.layers[0][0], None, None, None)
        ]
        rows = range(cut)
    elif side == "bottom":
        layer = [
            Node(initial_state(target_n), state, None, None, None)
            for state in automaton.layers[target_n]
        ]
        rows = range(target_n - 1, cut - 1, -1)
    else:
        raise ValueError("side must be top or bottom")
    stats = []
    for depth, row in enumerate(rows, 1):
        incoming_count = len(layer)
        children: dict[tuple, Node] = {}
        attempted = generated = cost_prunes = rank_prunes = alignment_edges = 0
        edges_by_state: dict[AlignmentState, list[AlignmentTransition]] = defaultdict(
            list
        )
        for edge in automaton.forward[row] if side == "top" else automaton.reverse[row]:
            edges_by_state[edge.before if side == "top" else edge.after].append(edge)
        constrained = _fixed_row(row, affine, fixed_rows, fixed_target)
        for node in layer:
            for edge in edges_by_state[node.alignment]:
                alignment_edges += 1
                next_alignment = edge.after if side == "top" else edge.before
                variants = row_domain_variants(
                    source[edge.source_row],
                    edge.seam,
                    radius,
                    constrained,
                    boundary_rewrites - node.boundary_rewrites,
                )
                if not variants:
                    continue
                minimum = _edge_row_minimum(
                    source,
                    edge,
                    radius,
                    constrained,
                    boundary_rewrites - node.boundary_rewrites,
                )
                assert minimum is not None
                other_minimum = (
                    suffix_cost[row + 1].get(next_alignment)
                    if side == "top"
                    else prefix_cost[row].get(next_alignment)
                )
                if (
                    other_minimum is None
                    or node.state.u_cost + minimum + other_minimum > u_count
                ):
                    cost_prunes += 1
                    continue
                for prefix_bits, suffix_bits, domains, delta in variants:
                    transitions, count = stream_row_packets(
                        node.state,
                        prefix_bits,
                        suffix_bits,
                        domains,
                        packet_alphabet=PACKET_ALPHABET,
                        u_cost_bounds=(None, u_count - other_minimum),
                    )
                    attempted += count
                    generated += len(transitions)
                    for transition in transitions:
                        if _rank_deficit_impossible(transition.outgoing, u_count):
                            rank_prunes += 1
                            continue
                        child = Node(
                            transition.outgoing,
                            next_alignment,
                            node,
                            transition.row_mask,
                            edge,
                            node.boundary_rewrites + delta,
                        )
                        key = exact_state_key(child)
                        old = children.get(key)
                        if old is None or child.state.u_cost < old.state.u_cost:
                            children[key] = child
        layer = list(children.values())
        item = SideRowStats(
            side,
            row,
            depth,
            incoming_count,
            alignment_edges,
            attempted,
            generated,
            len(layer),
            cost_prunes,
            rank_prunes,
        )
        stats.append(item)
        if report:
            print(json.dumps(asdict(item), sort_keys=True), flush=True)
        if not layer:
            break
    return layer, tuple(stats)


def build_bidirectional_frontiers(
    *,
    source: Sequence[str] | None = None,
    target_n: int = 17,
    radius: int = 1,
    u_limit: int = 179,
    cut: int = 8,
    fixed_rows: Sequence[int] = DEFAULT_FIXED_ROWS,
    fixed_target: Sequence[str] | None = None,
    schedule: str | ScheduleTemplate | CompatibleSchedule | None = None,
    boundary_rewrites: int = 0,
    report: bool = False,
) -> BidirectionalFrontiers:
    """Build complete top/bottom frontiers for all join budgets up to ``u_limit``."""
    started = time.monotonic()
    source = tuple(source or residue_two_pattern(14))
    if target_n != len(source) + 3 or not 1 <= cut < target_n:
        raise ValueError("invalid target size or cut")
    if boundary_rewrites not in (0, 1):
        raise ValueError("boundary_rewrites must be zero or one")
    if any(len(row) != len(source) for row in source):
        raise ValueError("source must be square")
    fixed_set = set(fixed_rows)
    affine = tuple(residue_two_affine_pattern(target_n)) if target_n >= 17 else None
    if fixed_set and affine is None:
        raise ValueError("affine fixed caps require target_n >= 17")
    if fixed_target is not None:
        fixed_target = tuple(fixed_target)
        if len(fixed_target) != target_n or any(
            len(row) != target_n for row in fixed_target
        ):
            raise ValueError("fixed target must be a target_n square")

    template, automaton = _resolve_schedule(schedule, source, target_n, radius)
    prefix_cost, suffix_cost = alignment_cost_bounds(
        automaton,
        source,
        radius,
        affine,
        fixed_set,
        fixed_target,
        boundary_rewrites,
    )
    common = dict(
        source=source,
        target_n=target_n,
        radius=radius,
        u_count=u_limit,
        cut=cut,
        automaton=automaton,
        prefix_cost=prefix_cost,
        suffix_cost=suffix_cost,
        affine=affine,
        fixed_rows=fixed_set,
        fixed_target=fixed_target,
        boundary_rewrites=boundary_rewrites,
        report=report,
    )
    top, top_stats = _expand_side(side="top", **common)
    bottom, bottom_stats = _expand_side(side="bottom", **common)
    if any(node.state.row_index != cut for node in top):
        raise AssertionError("top frontier has the wrong depth")
    if any(node.state.row_index != target_n - cut for node in bottom):
        raise AssertionError("bottom frontier has the wrong depth")
    if (
        top
        and bottom
        and top[0].state.row_index + bottom[0].state.row_index != target_n
    ):
        raise AssertionError("frontier depths do not sum to target height")
    return BidirectionalFrontiers(
        source,
        target_n,
        radius,
        u_limit,
        cut,
        tuple(sorted(fixed_set)),
        fixed_target,
        template.name if template else None,
        top,
        bottom,
        top_stats,
        bottom_stats,
        time.monotonic() - started,
        boundary_rewrites,
    )


def join_bidirectional_frontiers(
    frontiers: BidirectionalFrontiers,
    *,
    u_count: int,
    boundary_rewrites: int | None = None,
    bucketed: bool = True,
    use_cache: bool = True,
    report: bool = False,
) -> BidirectionalResult:
    """Exactly join prebuilt frontiers at any budget no greater than their limit."""
    started = time.monotonic()
    if u_count > frontiers.u_limit:
        raise ValueError("join budget exceeds the frontier construction limit")
    if boundary_rewrites is None:
        boundary_rewrites = frontiers.boundary_rewrites
    if boundary_rewrites not in (0, 1):
        raise ValueError("boundary_rewrites must be zero or one")
    if boundary_rewrites > frontiers.boundary_rewrites:
        raise ValueError(
            "boundary rewrite budget exceeds the frontier construction limit"
        )
    top = frontiers.top
    bottom = frontiers.bottom

    bottom_buckets: dict[AlignmentState, list[Node]] = defaultdict(list)
    for node in bottom:
        bottom_buckets[node.alignment].append(node)
    candidate_pairs = sum(len(bottom_buckets[node.alignment]) for node in top)
    scope_pruned = cost_pruned = merged = connected = cache_hits = merge_evaluations = 0
    winner: tuple[Node, Node] | None = None
    winner_rank: tuple[int, int] | None = None
    bottom_rank = {id(node): rank for rank, node in enumerate(bottom)}

    def visit(top_rank: int, top_node: Node, bottom_node: Node) -> None:
        nonlocal connected, winner, winner_rank, cache_hits, merge_evaluations
        key = (
            top_node.state.partition,
            bottom_node.state.partition,
            top_node.state.previous_u_mask & bottom_node.state.previous_u_mask,
        )
        if use_cache and key in frontiers.connectivity_cache:
            joined = frontiers.connectivity_cache[key]
            cache_hits += 1
        else:
            joined = merge_frontier_profile(top_node.state, bottom_node.state)[0] == 1
            merge_evaluations += 1
            if use_cache:
                frontiers.connectivity_cache[key] = joined
        if joined:
            connected += 1
            rank = (top_rank, bottom_rank[id(bottom_node)])
            if winner_rank is None or rank < winner_rank:
                winner = (top_node, bottom_node)
                winner_rank = rank

    if bucketed:
        cost_buckets = {}
        for alignment, nodes in bottom_buckets.items():
            grouped: dict[int, dict[int, list[Node]]] = defaultdict(
                lambda: defaultdict(list)
            )
            for node in nodes:
                grouped[node.boundary_rewrites][node.state.u_cost].append(node)
            lanes = {}
            for rewrites, by_cost in grouped.items():
                costs = sorted(by_cost)
                cumulative = []
                total = 0
                for cost in costs:
                    total += len(by_cost[cost])
                    cumulative.append(total)
                lanes[rewrites] = (costs, by_cost, cumulative, total)
            cost_buckets[alignment] = lanes
        for top_rank, top_node in enumerate(top):
            lanes = cost_buckets.get(top_node.alignment)
            if lanes is None:
                continue
            for rewrites, bucket in lanes.items():
                costs, grouped, cumulative, total = bucket
                if top_node.boundary_rewrites + rewrites > boundary_rewrites:
                    scope_pruned += total
                    continue
                end = bisect_right(costs, u_count - top_node.state.u_cost)
                feasible = cumulative[end - 1] if end else 0
                cost_pruned += total - feasible
                merged += feasible
                for cost in costs[:end]:
                    for bottom_node in grouped[cost]:
                        visit(top_rank, top_node, bottom_node)
    else:
        for top_rank, top_node in enumerate(top):
            for bottom_node in bottom_buckets[top_node.alignment]:
                if (
                    top_node.boundary_rewrites + bottom_node.boundary_rewrites
                    > boundary_rewrites
                ):
                    scope_pruned += 1
                    continue
                if top_node.state.u_cost + bottom_node.state.u_cost > u_count:
                    cost_pruned += 1
                    continue
                merged += 1
                visit(top_rank, top_node, bottom_node)

    witness = None
    steps = None
    validation = None
    if winner is not None:
        top_masks, top_edges = _path(winner[0])
        bottom_masks, bottom_edges = _path(winner[1], reverse=True)
        if len(top_masks) + len(bottom_masks) != frontiers.target_n:
            raise AssertionError("reconstructed row depths do not sum to target height")
        witness = tuple(
            render_mask(mask, frontiers.target_n)
            for mask in (*top_masks, *bottom_masks)
        )
        steps = _steps((*top_edges, *bottom_edges))
        observed_boundary_rewrites = replay_path(
            frontiers.source,
            witness,
            steps,
            frontiers.radius,
            boundary_rewrites,
        )
        validation = _validate_witness(witness, u_count)
        validation.update(
            {
                "boundary_rewrites": observed_boundary_rewrites,
                "boundary_rewrite_budget": boundary_rewrites,
                "within_boundary_rewrite_budget": (
                    observed_boundary_rewrites <= boundary_rewrites
                ),
            }
        )
        validation["accepted"] = (
            validation["accepted"] and validation["within_boundary_rewrite_budget"]
        )
        if not validation["accepted"]:
            raise AssertionError(
                f"independent validation rejected joined witness: {validation}"
            )
        conclusion = "SAT"
    else:
        conclusion = "UNSAT_IN_LANGUAGE"
    join_stats = JoinStats(
        len(bottom_buckets),
        candidate_pairs,
        cost_pruned,
        merged,
        connected,
        cache_hits,
        merge_evaluations,
        scope_pruned,
    )
    if report:
        print(json.dumps({"join": asdict(join_stats)}, sort_keys=True), flush=True)
    return BidirectionalResult(
        SCHEMA,
        len(frontiers.source),
        frontiers.target_n,
        frontiers.radius,
        u_count,
        frontiers.cut,
        frontiers.fixed_rows,
        frontiers.fixed_target is not None,
        frontiers.schedule,
        conclusion,
        True,
        frontiers.elapsed_seconds + time.monotonic() - started,
        len(top),
        len(bottom),
        witness,
        steps,
        validation,
        frontiers.top_stats,
        frontiers.bottom_stats,
        join_stats,
        boundary_rewrites,
    )


def search_bidirectional(
    *,
    source: Sequence[str] | None = None,
    target_n: int = 17,
    radius: int = 1,
    u_count: int = 179,
    cut: int = 8,
    fixed_rows: Sequence[int] = DEFAULT_FIXED_ROWS,
    fixed_target: Sequence[str] | None = None,
    schedule: str | ScheduleTemplate | CompatibleSchedule | None = None,
    boundary_rewrites: int = 0,
    report: bool = False,
    bucketed_join: bool = True,
    use_join_cache: bool = True,
) -> BidirectionalResult:
    """Run the complete exact top/bottom search and full-frontier join."""
    frontiers = build_bidirectional_frontiers(
        source=source,
        target_n=target_n,
        radius=radius,
        u_limit=u_count,
        cut=cut,
        fixed_rows=fixed_rows,
        fixed_target=fixed_target,
        schedule=schedule,
        boundary_rewrites=boundary_rewrites,
        report=report,
    )
    return join_bidirectional_frontiers(
        frontiers,
        u_count=u_count,
        boundary_rewrites=boundary_rewrites,
        bucketed=bucketed_join,
        use_cache=use_join_cache,
        report=report,
    )


def search(
    *,
    source: Sequence[str] | None = None,
    target_n: int = 17,
    radius: int = 1,
    u_count: int = 179,
    fixed_rows: Sequence[int] = DEFAULT_FIXED_ROWS,
    fixed_target: Sequence[str] | None = None,
    schedule: str | ScheduleTemplate | CompatibleSchedule | None = None,
    boundary_rewrites: int = 0,
    report: bool = False,
) -> SearchResult:
    """Run the complete exact search in the declared moving-seam language."""
    started = time.monotonic()
    source = tuple(source or residue_two_pattern(14))
    if target_n != len(source) + 3 or target_n < 2:
        raise ValueError("target_n must be source size plus three")
    if boundary_rewrites not in (0, 1):
        raise ValueError("boundary_rewrites must be zero or one")
    if any(len(row) != len(source) for row in source):
        raise ValueError("source must be square")
    affine = tuple(residue_two_affine_pattern(target_n)) if target_n >= 17 else None
    fixed_set = set(fixed_rows)
    if fixed_set and affine is None:
        raise ValueError("affine fixed caps require target_n >= 17")
    if fixed_target is not None:
        fixed_target = tuple(fixed_target)
        if len(fixed_target) != target_n or any(
            len(row) != target_n for row in fixed_target
        ):
            raise ValueError("fixed target must be a target_n square")

    template, automaton = _resolve_schedule(schedule, source, target_n, radius)
    layer = [Node(initial_state(target_n), automaton.layers[0][0], None, None, None)]
    stats = []
    for target_row in range(target_n):
        incoming_count = len(layer)
        children: dict[tuple, Node] = {}
        attempted = generated = cost_prunes = rank_prunes = 0
        edges_by_before: dict[AlignmentState, list[AlignmentTransition]] = defaultdict(
            list
        )
        for edge in automaton.forward[target_row]:
            edges_by_before[edge.before].append(edge)
        for node in layer:
            for edge in edges_by_before[node.alignment]:
                constrained = (
                    fixed_target[target_row]
                    if fixed_target is not None
                    else (affine[target_row] if target_row in fixed_set else None)
                )
                variants = row_domain_variants(
                    source[edge.source_row],
                    edge.seam,
                    radius,
                    constrained,
                    boundary_rewrites - node.boundary_rewrites,
                )
                if not variants:
                    continue
                minimum_row_u = min(
                    prefix.count("U")
                    + suffix.count("U")
                    + sum(
                        min(PACKET_ALPHABET[name].count("U") for name in domain)
                        for domain in domains
                    )
                    for prefix, suffix, domains, _ in variants
                )
                if node.state.u_cost + minimum_row_u > u_count:
                    cost_prunes += 1
                    continue
                for prefix, suffix, domains, delta in variants:
                    transitions, count = stream_row_packets(
                        node.state,
                        prefix,
                        suffix,
                        domains,
                        packet_alphabet=PACKET_ALPHABET,
                        u_cost_bounds=(None, u_count),
                    )
                    attempted += count
                    generated += len(transitions)
                    for transition in transitions:
                        if _rank_deficit_impossible(transition.outgoing, u_count):
                            rank_prunes += 1
                            continue
                        child = Node(
                            transition.outgoing,
                            edge.after,
                            node,
                            transition.row_mask,
                            edge,
                            node.boundary_rewrites + delta,
                        )
                        key = exact_state_key(child)
                        old = children.get(key)
                        if old is None or child.state.u_cost < old.state.u_cost:
                            children[key] = child
        layer = list(children.values())
        row_stats = RowStats(
            target_row,
            incoming_count,
            attempted,
            generated,
            len(layer),
            cost_prunes,
            rank_prunes,
        )
        stats.append(row_stats)
        if report:
            print(json.dumps(asdict(row_stats), sort_keys=True))
        if not layer:
            break

    accepted = None
    validation = None
    accepted_rows = None
    accepted_steps = None
    for node in layer if len(stats) == target_n else ():
        if node.alignment.cursor != len(source) or node.alignment.holds != 3:
            continue
        masks, transitions = _path(node)
        rows = tuple(render_mask(mask, target_n) for mask in masks)
        candidate_validation = _validate_witness(rows, u_count)
        observed_boundary_rewrites = replay_path(
            source,
            rows,
            _steps(transitions),
            radius,
            boundary_rewrites,
        )
        candidate_validation.update(
            {
                "boundary_rewrites": observed_boundary_rewrites,
                "boundary_rewrite_budget": boundary_rewrites,
                "within_boundary_rewrite_budget": (
                    observed_boundary_rewrites <= boundary_rewrites
                ),
            }
        )
        candidate_validation["accepted"] = (
            candidate_validation["accepted"]
            and candidate_validation["within_boundary_rewrite_budget"]
        )
        if candidate_validation["accepted"]:
            accepted, validation = node, candidate_validation
            accepted_rows, accepted_steps = rows, _steps(transitions)
            break
    if accepted is not None:
        assert accepted_rows is not None and accepted_steps is not None
        replay_path(source, accepted_rows, accepted_steps, radius, boundary_rewrites)
        conclusion = "SAT"
    else:
        conclusion = "UNSAT_IN_LANGUAGE"
    return SearchResult(
        SCHEMA,
        len(source),
        target_n,
        radius,
        u_count,
        tuple(sorted(fixed_set)),
        fixed_target is not None,
        template.name if template else None,
        conclusion,
        True,
        time.monotonic() - started,
        len(layer) if len(stats) == target_n else 0,
        accepted_rows,
        accepted_steps,
        validation,
        tuple(stats),
        boundary_rewrites,
    )


def result_record(result: SearchResult | BidirectionalResult) -> dict:
    record = asdict(result)
    record["boundary_rewrite_budget"] = result.boundary_rewrites
    return record


def compatible_schedule_record(schedule: CompatibleSchedule) -> dict:
    return {
        "name": schedule.name,
        "calibration_radius": schedule.calibration_radius,
        "complete_path_count": schedule.complete_path_count,
        "layer_state_counts": list(schedule.layer_state_counts),
        "layer_edge_counts": list(schedule.layer_edge_counts),
        "metadata": schedule.metadata,
    }


def write_result(path: Path, record: dict) -> None:
    """Write completed JSON through a same-directory temporary replacement."""
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary_name = None
    try:
        with tempfile.NamedTemporaryFile(
            "w",
            encoding="utf-8",
            dir=path.parent,
            prefix=f".{path.name}.",
            delete=False,
        ) as temporary:
            temporary_name = temporary.name
            json.dump(record, temporary, indent=2, sort_keys=True)
            temporary.write("\n")
            temporary.flush()
            os.fsync(temporary.fileno())
        os.replace(temporary_name, path)
    finally:
        if temporary_name is not None and os.path.exists(temporary_name):
            os.unlink(temporary_name)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--u-count", type=int, default=179)
    parser.add_argument("--radius", type=int, default=1)
    parser.add_argument("--boundary-rewrites", type=int, choices=(0, 1), default=0)
    parser.add_argument("--bidirectional", action="store_true")
    parser.add_argument("--cut", type=int, default=8)
    parser.add_argument(
        "--schedule",
        choices=(
            "affine",
            "affine-compatible",
            "affine-holds-compatible",
            "affine-one-hold-relocation",
            "affine-two-hold-relocation",
        ),
    )
    parser.add_argument(
        "--output", type=Path, help="atomically write the completed JSON result"
    )
    parser.add_argument("--json", action="store_true")
    parser.add_argument(
        "--quiet", action="store_true", help="suppress per-row progress"
    )
    args = parser.parse_args()
    search_function = search_bidirectional if args.bidirectional else search
    compatible_builders = {
        "affine-compatible": affine_compatible_schedule,
        "affine-holds-compatible": affine_holds_compatible_schedule,
        "affine-one-hold-relocation": affine_one_hold_relocation_schedule,
        "affine-two-hold-relocation": affine_two_hold_relocation_schedule,
    }
    compatible = (
        compatible_builders[args.schedule]()
        if args.schedule in compatible_builders
        else None
    )
    options = {
        "u_count": args.u_count,
        "radius": args.radius,
        "boundary_rewrites": args.boundary_rewrites,
        "schedule": compatible or args.schedule,
        "report": not args.quiet and not args.json,
    }
    if args.bidirectional:
        options["cut"] = args.cut
    result = search_function(**options)
    record = result_record(result)
    if compatible is not None:
        record["schedule_automaton"] = compatible_schedule_record(compatible)
    if args.output is not None:
        write_result(args.output, record)
    if args.json:
        print(json.dumps(record, indent=2, sort_keys=True))
    else:
        summary_keys = ["conclusion", "complete", "elapsed_seconds", "validation"]
        summary_keys += (
            ["top_states", "bottom_states", "join_stats"]
            if args.bidirectional
            else ["final_states"]
        )
        print(json.dumps({key: record[key] for key in summary_keys}, indent=2))
        if result.witness:
            print("\n".join(result.witness))


if __name__ == "__main__":
    main()
