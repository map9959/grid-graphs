#!/usr/bin/env python3
"""Finite equality-only carrier grammar for residue-two frontiers.

For n=3k+2, group zero is the single left frontier face and groups 1..k
are the consecutive triples to its right.  A partition is accepted exactly
when every non-OUT component occupies an interval of groups and every group
cut is crossed by at most one such component.

The census below is finite evidence, not a zero-slack coverage proof.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter, defaultdict
from dataclasses import asdict, dataclass
from pathlib import Path

from analysis._paths import analysis_path
from analysis.patterns.diagonal_patterns import (
    residue_two_affine_pattern,
    residue_two_explicit_pattern,
)
from analysis.tiles.tile_grammar import (
    FrontierState,
    advance_row,
    initial_state,
    row_mask,
)
from analysis.transport.equality_corridor import (
    EqualityCorridor,
    build_equality_corridor,
    structural_key,
)

SCHEMA = "grid-graphs.residue-two-carrier-grammar.v1"
DEFAULT_OUTPUT = analysis_path("residue_two_carrier_grammar.json")


def canonical_rooted_partition(partition: tuple[int, ...]) -> tuple[int, ...]:
    """Relabel a nonempty partition by OUT-first frontier occurrence."""
    if not partition:
        raise ValueError("a rooted partition must contain OUT")
    labels = {partition[0]: 0}
    canonical = []
    for label in partition:
        labels.setdefault(label, len(labels))
        canonical.append(labels[label])
    return tuple(canonical)


def packet_groups(n: int) -> tuple[tuple[int, ...], ...]:
    """Return exact zero-based frontier-face slots in groups 0..k."""
    if n < 5 or n % 3 != 2:
        raise ValueError("carrier grammar requires n=3k+2 with k>=1")
    k = (n - 2) // 3
    return ((0,), *(tuple(range(3 * group - 2, 3 * group + 1)) for group in range(1, k + 1)))


@dataclass(frozen=True, slots=True)
class ComponentEvent:
    component: int
    group: int
    face_slots: tuple[int, ...]
    role: str


@dataclass(frozen=True, slots=True)
class CarrierEvent:
    cut: int
    component: int


@dataclass(frozen=True, slots=True)
class CarrierRecord:
    """Lossless component events plus the carriers derived at group cuts."""

    width: int
    frontier_slots: int
    events: tuple[ComponentEvent, ...]
    carriers: tuple[CarrierEvent, ...]


@dataclass(frozen=True, slots=True)
class SupportHole:
    component: int
    occupied_groups: tuple[int, ...]
    missing_groups: tuple[int, ...]


@dataclass(frozen=True, slots=True)
class ConcurrentCarriers:
    cut: int
    components: tuple[int, ...]


@dataclass(frozen=True, slots=True)
class GrammarMetrics:
    non_out_components: int
    occupied_group_events: int
    carrier_events: int
    maximum_concurrent_carriers: int
    maximum_group_span: int
    support_holes: int


@dataclass(frozen=True, slots=True)
class Recognition:
    accepted: bool
    record: CarrierRecord
    support_holes: tuple[SupportHole, ...]
    concurrent_carriers: tuple[ConcurrentCarriers, ...]
    metrics: GrammarMetrics


def _record_from_partition(n: int, partition: tuple[int, ...]) -> tuple[CarrierRecord, dict[int, tuple[int, ...]], dict[int, tuple[int, ...]]]:
    groups = packet_groups(n)
    if len(partition) not in (1, n):
        raise ValueError("partition must be terminal/top or contain OUT plus n-1 frontier faces")
    faces = partition[1:]
    group_of_slot = {slot: group for group, slots in enumerate(groups) for slot in slots}
    slots_by_component: dict[int, list[int]] = defaultdict(list)
    for slot, component in enumerate(faces):
        if component:
            slots_by_component[component].append(slot)

    occupied = {
        component: tuple(sorted({group_of_slot[slot] for slot in slots}))
        for component, slots in slots_by_component.items()
    }
    events = []
    for component in sorted(slots_by_component):
        support = occupied[component]
        for index, group in enumerate(support):
            if len(support) == 1:
                role = "single"
            elif index == 0:
                role = "open"
            elif index + 1 == len(support):
                role = "close"
            else:
                role = "carry"
            exact_slots = tuple(slot for slot in slots_by_component[component] if group_of_slot[slot] == group)
            events.append(ComponentEvent(component, group, exact_slots, role))

    carriers = []
    crossing: dict[int, tuple[int, ...]] = {}
    for cut in range(len(groups) - 1):
        components = tuple(
            component
            for component, support in sorted(occupied.items())
            if min(support) <= cut < max(support)
        )
        crossing[cut] = components
        carriers.extend(CarrierEvent(cut, component) for component in components)
    return CarrierRecord(n, len(faces), tuple(events), tuple(carriers)), occupied, crossing


def recognize_partition(n: int, partition: tuple[int, ...]) -> Recognition:
    """Recognize a rooted partition modulo component-label renaming."""
    canonical = canonical_rooted_partition(partition)
    record, occupied, crossing = _record_from_partition(n, canonical)
    holes = tuple(
        SupportHole(
            component,
            support,
            tuple(group for group in range(min(support), max(support) + 1) if group not in support),
        )
        for component, support in sorted(occupied.items())
        if len(support) != max(support) - min(support) + 1
    )
    concurrent = tuple(
        ConcurrentCarriers(cut, components)
        for cut, components in crossing.items()
        if len(components) > 1
    )
    spans = [max(support) - min(support) + 1 for support in occupied.values()]
    metrics = GrammarMetrics(
        non_out_components=len(occupied),
        occupied_group_events=len(record.events),
        carrier_events=len(record.carriers),
        maximum_concurrent_carriers=max(map(len, crossing.values()), default=0),
        maximum_group_span=max(spans, default=0),
        support_holes=sum(len(reason.missing_groups) for reason in holes),
    )
    return Recognition(not holes and not concurrent, record, holes, concurrent, metrics)


def expand_carrier_record(record: CarrierRecord) -> tuple[int, ...]:
    """Validate and expand a carrier/event record to its canonical partition."""
    packet_groups(record.width)
    if record.frontier_slots not in (0, record.width - 1):
        raise ValueError("record has the wrong frontier slot count")
    faces = [0] * record.frontier_slots
    for event in record.events:
        if event.component <= 0 or event.role not in ("single", "open", "carry", "close"):
            raise ValueError("invalid component event")
        for slot in event.face_slots:
            if not 0 <= slot < record.frontier_slots or faces[slot]:
                raise ValueError("component events overlap or address an invalid slot")
            faces[slot] = event.component
    partition = (0, *faces)
    if canonical_rooted_partition(partition) != partition:
        raise ValueError("component events are not canonically rooted")
    expected, _, _ = _record_from_partition(record.width, partition)
    if expected != record:
        raise ValueError("event roles, groups, or carriers are inconsistent")
    return partition


def recognize_state(state: FrontierState) -> Recognition:
    return recognize_partition(state.n, state.partition)


def _fixed_trace(width: int) -> list[FrontierState]:
    rows = residue_two_affine_pattern(width) if width == 17 else residue_two_explicit_pattern(width)
    state = initial_state(width)
    trace = [state]
    for index, row in enumerate(rows):
        state = advance_row(state, row_mask(row))
        if state is None:
            raise AssertionError(f"fixed n={width} trace failed at row {index}")
        trace.append(state)
    return trace


def _histogram(values) -> dict[str, int]:
    return {str(key): value for key, value in sorted(Counter(values).items())}


def _state_census(states: list[FrontierState]) -> dict:
    accepted = holes = concurrent = round_trips = 0
    reason_combinations = Counter()
    metrics = defaultdict(list)
    for state in states:
        result = recognize_state(state)
        accepted += result.accepted
        holes += bool(result.support_holes)
        concurrent += bool(result.concurrent_carriers)
        labels = []
        if result.support_holes:
            labels.append("support_hole")
        if result.concurrent_carriers:
            labels.append("concurrent_carriers")
        reason_combinations["+".join(labels) or "accepted"] += 1
        if expand_carrier_record(result.record) != canonical_rooted_partition(state.partition):
            raise AssertionError("carrier record failed exact round trip")
        round_trips += 1
        for field, value in asdict(result.metrics).items():
            metrics[field].append(value)
    return {
        "states": len(states),
        "accepted": accepted,
        "excluded": len(states) - accepted,
        "states_with_support_holes": holes,
        "states_with_concurrent_carriers": concurrent,
        "reason_combinations": dict(sorted(reason_combinations.items())),
        "lossless_round_trips": round_trips,
        "metric_histograms": {field: _histogram(values) for field, values in sorted(metrics.items())},
    }


def _transition_census(corridor: EqualityCorridor) -> dict:
    equality_edges = {
        (row, edge.incoming, edge.mask, edge.outgoing)
        for row, edges in enumerate(corridor.corridor_edges)
        for edge in edges
    }
    cache: dict[tuple[int, ...], bool] = {}

    def accepted(partition: tuple[int, ...]) -> bool:
        if partition not in cache:
            cache[partition] = recognize_partition(corridor.n, partition).accepted
        return cache[partition]

    incoming_states = attempted = valid = staying = leaving = exact = completable = dead_end = 0
    slack = Counter()
    for row in range(corridor.n):
        for incoming_key, incoming in corridor.layers[row].items():
            if not accepted(incoming.partition):
                continue
            incoming_states += 1
            for mask in range(1 << corridor.n):
                attempted += 1
                outgoing = advance_row(incoming, mask)
                if outgoing is None:
                    continue
                valid += 1
                outgoing_key = structural_key(outgoing)
                is_staying = accepted(outgoing.partition)
                staying += is_staying
                leaving += not is_staying
                edge_id = (row, incoming_key, mask, outgoing_key)
                exact += edge_id in equality_edges
                suffix = corridor.backward[row + 1].get(outgoing_key)
                if suffix is None:
                    dead_end += 1
                    continue
                completable += 1
                u_count = mask.bit_count()
                runs = (mask & ~(mask << 1)).bit_count()
                vertical = (incoming.previous_u_mask & mask).bit_count()
                cycles = outgoing.cycle_excess - incoming.cycle_excess
                weight = u_count + 2 * runs - 2 * vertical + 2 * cycles - 1
                reduced_slack = corridor.forward[row][incoming_key] + weight + suffix - corridor.minimum_weight
                if reduced_slack < 0:
                    raise AssertionError("fixed-width reduced slack became negative")
                slack[reduced_slack] += 1
    return {
        "grammar_incoming_states": incoming_states,
        "masks_attempted": attempted,
        "frontier_accepted_transitions": valid,
        "staying_in_grammar": staying,
        "leaving_grammar": leaving,
        "exact_equality_corridor_edges": exact,
        "total_equality_corridor_edges": len(equality_edges),
        "completable_transitions_with_sound_slack": completable,
        "dead_end_transitions_without_slack": dead_end,
        "fixed_width_reduced_slack_histogram": _histogram(slack.elements()),
    }


def build_artifact() -> dict:
    corridors = {n: build_equality_corridor(n) for n in (5, 8)}
    sources = {}
    for n, corridor in corridors.items():
        sources[f"n{n}-complete-equality-corridor"] = _state_census(
            [corridor.layers[row][key] for row, keys in enumerate(corridor.corridor_states) for key in keys]
        )
        sources[f"n{n}-full-structurally-reachable-layers"] = _state_census(
            [state for layer in corridor.layers for state in layer.values()]
        )
    for n in (11, 14, 17):
        kind = "near-equality-179-U" if n == 17 else "equality"
        sources[f"n{n}-fixed-{kind}-trace"] = _state_census(_fixed_trace(n))

    return {
        "schema": SCHEMA,
        "scope": {
            "semantics": "finite-equality-only-structural-grammar-evidence",
            "complete_equality_corridors": [5, 8],
            "complete_structurally_reachable_layers": [5, 8],
            "fixed_equality_traces": [11, 14],
            "near_equality_control": {"width": 17, "u_count": 179},
            "zero_slack_coverage_proof": False,
        },
        "definitions": {
            "groups": "group 0 is frontier face slot 0; group i=1..k is slots 3i-2 through 3i",
            "support_rule": "every non-OUT component occupies a contiguous set of groups",
            "carrier_rule": "at each cut between adjacent groups at most one non-OUT component occupies groups on both sides",
            "equality_only": "recognition reads only n and the rooted connectivity partition",
            "record": "canonical component/group events retain exact frontier slots; cut carrier events are checked on expansion",
            "fixed_width_reduced_slack": "minimum prefix distance + row weight + minimum suffix distance - width minimum; reported only when a suffix exists",
        },
        "sources": sources,
        "row_transitions": {str(n): _transition_census(corridor) for n, corridor in corridors.items()},
        "limitations": [
            "This is finite evidence, not a zero-slack coverage proof.",
            "Only n=5 and n=8 use complete equality corridors and complete operational reachable layers.",
            "The n=11 and n=14 equality data and n=17 179-U control are single fixed traces.",
            "Reduced slack is a fixed-width diagnostic and is omitted for transitions with no accepting suffix.",
        ],
        "provenance": {
            "producer": "analysis/residue_certificates/residue_two_carrier_grammar.py",
            "command": ["python3", "-B", "-m",
                                         'analysis.residue_certificates.residue_two_carrier_grammar', "--output", "analysis/residue_two_carrier_grammar.json"],
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
        print(f"finite carrier grammar evidence matches {args.output}")
    else:
        if args.output is not None:
            args.output.write_text(rendered)
        print(rendered, end="")


if __name__ == "__main__":
    main()
