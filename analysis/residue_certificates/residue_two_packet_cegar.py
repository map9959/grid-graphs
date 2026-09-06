#!/usr/bin/env python3
"""Observed packet-signature refinements on the n=5,8 equality corridors.

This is a finite-width collision audit, not a certificate for other widths.
For n=3k+2, columns 1..n-2 are read left-to-right as k three-bit packets;
columns 0 and n-1 are the two cap bits.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import defaultdict
from pathlib import Path
from typing import Callable, Iterable

from analysis.transport.equality_corridor import build_equality_corridor
from analysis.residue_certificates.residue_two_equality_cegar import ObservedState, observe_corridor
from analysis.tiles.tile_grammar import FrontierState


SCHEMA = "grid-graphs.residue-two-packet-cegar.v1"
WIDTHS = (5, 8)
LEVELS = (
    "packet_words",
    "packet_local",
    "packet_carry",
    "packet_global_carry",
    "packet_carry_positioned",
    "rooted_packet_control",
)
WIDTH_DEPENDENT_FIELDS = {
    "packet_words": ("ordered_packet_sequence_length",),
    "packet_local": ("ordered_packet_sequence_length",),
    "packet_carry": ("ordered_packet_sequence_length",),
    "packet_global_carry": (
        "ordered_packet_sequence_length",
        "unbounded_rooted_component_labels",
    ),
    "packet_carry_positioned": (
        "ordered_packet_sequence_length",
        "absolute_row",
        "rows_to_bottom",
    ),
    "rooted_packet_control": (
        "width",
        "absolute_row",
        "full_previous_u_mask",
        "full_rooted_partition",
    ),
}


def _boundary_mode(state: FrontierState) -> str:
    if state.row_index == 0:
        return "top"
    if state.row_index == state.n:
        return "terminal"
    if state.row_index + 1 == state.n:
        return "bottom"
    return "bulk"


def packet_words(state: FrontierState) -> tuple[int, ...]:
    """Return ordered little-endian three-bit words from the interior."""
    if state.n % 3 != 2:
        raise ValueError("packet words require n=3k+2")
    return tuple((state.previous_u_mask >> (1 + 3 * packet)) & 0b111
                 for packet in range((state.n - 2) // 3))


def _rooted_restriction(state: FrontierState, slots: tuple[int, ...]) -> tuple[int, ...]:
    """Canonicalize selected frontier-face slots with OUT rooted at zero."""
    partition = state.partition
    if len(partition) == 1:
        return ()
    out = partition[0]
    labels = {out: 0}
    restricted = []
    for slot in slots:
        label = partition[slot + 1]
        if label not in labels:
            labels[label] = len(labels)
        restricted.append(labels[label])
    return tuple(restricted)


def packet_local_restrictions(state: FrontierState) -> tuple[tuple[int, ...], ...]:
    """Rooted partition restrictions on each ordered interior packet."""
    return tuple(
        _rooted_restriction(state, tuple(range(1 + 3 * p, 4 + 3 * p)))
        for p in range((state.n - 2) // 3)
    )


def packet_carry_signatures(state: FrontierState) -> tuple[tuple[int, ...], ...]:
    """Rooted restrictions crossing each cap/packet or packet/packet cut.

    A boundary signature sees the left-cap face and first packet (four slots),
    both adjacent packets (six slots), or the final packet beside the right
    cap bit. Thus carried component identity survives the independent local
    renaming of non-OUT components.
    """
    packets = (state.n - 2) // 3
    if not packets:
        return ()
    windows = [(0, *range(1, 4))]
    windows.extend(
        tuple(range(1 + 3 * (p - 1), 4 + 3 * p)) for p in range(1, packets)
    )
    windows.append(tuple(range(state.n - 4, state.n - 1)))
    return tuple(_rooted_restriction(state, tuple(window)) for window in windows)


def packet_global_carry(state: FrontierState) -> tuple[int, tuple[tuple[int, ...], ...]]:
    """Return the lossless rooted partition word grouped by packet.

    Unlike independently canonicalized local windows, these labels retain
    component identity across arbitrarily separated packets. The tuple grows
    with width and is an exact symbolic word, not bounded finite control.
    """
    if len(state.partition) == 1:
        return 0, ()
    rooted = _rooted_restriction(state, tuple(range(state.n - 1)))
    left_face = rooted[0]
    packets = tuple(
        rooted[1 + 3 * packet : 4 + 3 * packet]
        for packet in range((state.n - 2) // 3)
    )
    if 1 + 3 * len(packets) != len(rooted):
        raise AssertionError("packetized rooted partition did not cover every face")
    return left_face, packets


def packet_signature(state: FrontierState, level: str) -> tuple:
    """Return one key in the declared packet refinement hierarchy."""
    cap_bits = (
        bool(state.previous_u_mask & 1),
        bool(state.previous_u_mask & (1 << (state.n - 1))),
    )
    common = (state.row_index % 3, _boundary_mode(state), cap_bits, packet_words(state))
    if level == "packet_words":
        return common
    local = (*common, packet_local_restrictions(state))
    if level == "packet_local":
        return local
    carry = (*local, packet_carry_signatures(state))
    if level == "packet_carry":
        return carry
    if level == "packet_global_carry":
        return (*common, packet_global_carry(state))
    if level == "packet_carry_positioned":
        # These cap-position fields intentionally sacrifice width independence.
        return (*carry, state.row_index, state.n - state.row_index)
    if level == "rooted_packet_control":
        return (state.n, state.row_index, state.previous_u_mask, state.partition)
    raise ValueError(f"unknown packet signature level: {level}")


def _jsonable(value):
    if isinstance(value, (tuple, list)):
        return [_jsonable(item) for item in value]
    if isinstance(value, (set, frozenset)):
        return [_jsonable(item) for item in sorted(value, key=repr)]
    return value


def _digest(value) -> str:
    payload = json.dumps(_jsonable(value), separators=(",", ":"), sort_keys=True)
    return hashlib.sha256(payload.encode("ascii")).hexdigest()[:16]


def _pair(
    states: list[ObservedState],
    predicate: Callable[[ObservedState, ObservedState], bool],
) -> tuple[ObservedState, ObservedState] | None:
    for index, left in enumerate(states):
        for right in states[index + 1:]:
            if predicate(left, right) and left.behavior != right.behavior:
                return left, right
    return None


def _witness(pair: tuple[ObservedState, ObservedState] | None) -> dict | None:
    if pair is None:
        return None
    left, right = pair
    return {
        "state_ids": [left.identifier, right.identifier],
        "widths": [left.width, right.width],
        "boundary_modes": [_boundary_mode(left.state), _boundary_mode(right.state)],
        "outgoing_labels_differ": left.outgoing_labels != right.outgoing_labels,
        "accepting_suffixes_differ": left.accepting_suffixes != right.accepting_suffixes,
        "behavior_digests": [_digest(left.behavior), _digest(right.behavior)],
    }


COLLISION_KINDS = (
    "within_width_bulk",
    "within_width_cap",
    "cross_width_bulk",
    "cross_width_cap",
)


def collision_report(observations: Iterable[ObservedState], level: str) -> dict:
    """Compare complete observed behaviors in every packet-signature class."""
    groups: dict[tuple, list[ObservedState]] = defaultdict(list)
    for observed in observations:
        groups[packet_signature(observed.state, level)].append(observed)

    counts = {kind: 0 for kind in COLLISION_KINDS}
    witnesses = {kind: None for kind in COLLISION_KINDS}
    collision_groups = 0
    merged_groups = 0
    predicates = {
        "within_width_bulk": lambda a, b: a.width == b.width
        and _boundary_mode(a.state) == _boundary_mode(b.state) == "bulk",
        "within_width_cap": lambda a, b: a.width == b.width
        and _boundary_mode(a.state) == _boundary_mode(b.state) != "bulk",
        "cross_width_bulk": lambda a, b: a.width != b.width
        and _boundary_mode(a.state) == _boundary_mode(b.state) == "bulk",
        "cross_width_cap": lambda a, b: a.width != b.width
        and _boundary_mode(a.state) == _boundary_mode(b.state) != "bulk",
    }
    for states in groups.values():
        states.sort(key=lambda item: item.identifier)
        merged_groups += len(states) > 1
        if len({item.behavior for item in states}) == 1:
            continue
        collision_groups += 1
        for kind, predicate in predicates.items():
            pair = _pair(states, predicate)
            if pair is not None:
                counts[kind] += 1
                if witnesses[kind] is None:
                    witnesses[kind] = _witness(pair)
    return {
        "keys": len(groups),
        "merged_groups": merged_groups,
        "collision_groups": collision_groups,
        "collision_groups_by_kind": counts,
        "first_witness_by_kind": witnesses,
    }


def build_artifact() -> dict:
    corridors = {n: build_equality_corridor(n) for n in WIDTHS}
    by_width = {n: observe_corridor(corridors[n]) for n in WIDTHS}
    observations = [item for n in WIDTHS for item in by_width[n]]
    hierarchy = {level: collision_report(observations, level) for level in LEVELS}
    zero_bulk = next(
        (level for level in LEVELS
         if hierarchy[level]["collision_groups_by_kind"]["within_width_bulk"] == 0),
        None,
    )
    if hierarchy["rooted_packet_control"]["collision_groups"]:
        raise AssertionError("exact rooted packet control unexpectedly collided")
    return {
        "schema": SCHEMA,
        "scope": {
            "semantics": "finite-width-complete-equality-corridor-diagnostic-only",
            "widths": list(WIDTHS),
            "theorem_or_certificate": False,
            "coverage_beyond_enumerated_widths_claimed": False,
        },
        "definitions": {
            "packet_layout": "for n=3k+2, ordered 3-bit words cover columns 1..n-2; columns 0 and n-1 are caps",
            "packet_word_bit_order": "least-significant bit is the leftmost packet column",
            "packet_local_restriction": "rooted canonical partition restriction to the three frontier-face slots assigned to the packet after the left cap face",
            "carry_signature": "rooted canonical restriction to the left-cap/packet, packet/packet, and final-packet windows; cap U bits are separate signature fields",
            "global_carry_word": "lossless rooted component labels for the left face and each ordered three-face packet; variable-length and not bounded finite control",
            "state_behavior": "complete outgoing normalized equality-edge labels and complete accepting-suffix label words",
            "cap_state": "top, bottom, or terminal boundary mode",
            "hierarchy": list(LEVELS),
            "width_dependent_fields_by_level": {
                level: list(WIDTH_DEPENDENT_FIELDS[level]) for level in LEVELS
            },
        },
        "corridors": {
            str(n): {
                "packets": (n - 2) // 3,
                "states": len(by_width[n]),
                "transitions": sum(map(len, corridors[n].corridor_edges)),
                "minimum_path_count": str(corridors[n].minimum_path_count),
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
        "smallest_tested_zero_within_width_bulk": zero_bulk,
        "first_lossless_packet_level": "packet_global_carry",
        "provenance": {
            "producer": "analysis/residue_certificates/residue_two_packet_cegar.py",
            "command": ["python3", "-B", "analysis/residue_certificates/residue_two_packet_cegar.py", "--output",
                        "analysis/residue_two_packet_cegar.json"],
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
        print(f"packet CEGAR diagnostic matches {args.output}")
    else:
        if args.output is not None:
            args.output.write_text(rendered)
        print(rendered, end="")


if __name__ == "__main__":
    main()
