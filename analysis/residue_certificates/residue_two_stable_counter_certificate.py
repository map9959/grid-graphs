#!/usr/bin/env python3
"""Symbolic affine counter certificates for the stable residue-two rules.

This proves the counter formulas for every packet length at least seven.  It
does not prove that the compact source/action pair advances to the claimed
target partition; that topological transport remains a separate obligation.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, TypeVar

from analysis.patterns.diagonal_patterns import residue_two_affine_pattern
from analysis.residue_certificates.residue_two_affine_motif_grammar import (
    BoundaryDefectAtom,
)
from analysis.residue_certificates.residue_two_compact_transition import (
    ActionKey,
    AffineDeltas,
    AffineValue,
    ControlKey,
    structural_key,
    trace_observations,
)

T = TypeVar("T")


@dataclass(frozen=True, slots=True)
class StableCounterCertificate:
    source: ControlKey
    action: ActionKey
    target: ControlKey
    deltas: AffineDeltas


def _add(*values: AffineValue) -> AffineValue:
    return AffineValue(
        sum(value.packet_coefficient for value in values),
        sum(value.constant for value in values),
    )


def _subtract(left: AffineValue, right: AffineValue) -> AffineValue:
    return AffineValue(
        left.packet_coefficient - right.packet_coefficient,
        left.constant - right.constant,
    )


def boundary_values(
    dominant: T, exceptions: tuple[tuple[str, T], ...]
) -> tuple[tuple[T, T], tuple[T, T, T, T]]:
    """Return packets L0,L1 and R3,R2,R1,R0 for every length at least seven."""
    left = [dominant, dominant]
    right = [dominant, dominant, dominant, dominant]
    seen: set[str] = set()
    for endpoint, value in exceptions:
        if endpoint in seen:
            raise ValueError(f"duplicate endpoint {endpoint}")
        seen.add(endpoint)
        if endpoint in ("L0", "L1"):
            left[int(endpoint[1])] = value
        elif endpoint in ("R0", "R1", "R2", "R3"):
            right[3 - int(endpoint[1])] = value
        else:
            raise ValueError(f"unknown endpoint {endpoint}")
    return (left[0], left[1]), (right[0], right[1], right[2], right[3])


def _regular_point_sum(
    dominant: T,
    exceptions: tuple[tuple[str, T], ...],
    score: Callable[[T], int],
) -> AffineValue:
    left, right = boundary_values(dominant, exceptions)
    dominant_score = score(dominant)
    return AffineValue(
        dominant_score,
        sum(score(value) for value in (*left, *right)) - 6 * dominant_score,
    )


def _packet_bits(packet: int) -> tuple[int, int, int]:
    if type(packet) is not int or not 0 <= packet < 8:
        raise ValueError("packet must be a three-bit integer")
    return tuple((packet >> offset) & 1 for offset in range(3))


def action_u(action: ActionKey) -> AffineValue:
    packets = _regular_point_sum(
        action.dominant_packet,
        action.exceptions,
        lambda packet: packet.bit_count(),
    )
    return _add(packets, AffineValue(0, sum(action.cap_bits)))


def horizontal_edges(action: ActionKey) -> AffineValue:
    """Count adjacent U pairs in the regular action word."""
    left, right = boundary_values(action.dominant_packet, action.exceptions)
    dominant = action.dominant_packet

    def internal(packet: int) -> int:
        bits = _packet_bits(packet)
        return bits[0] * bits[1] + bits[1] * bits[2]

    def crossing(first: int, second: int) -> int:
        return _packet_bits(first)[2] * _packet_bits(second)[0]

    coefficient = internal(dominant) + crossing(dominant, dominant)
    constant = sum(internal(value) for value in (*left, *right))
    constant -= 6 * internal(dominant)
    constant -= 7 * crossing(dominant, dominant)
    chain = (left[0], left[1], dominant, right[0], *right[1:])
    constant += sum(crossing(first, second) for first, second in zip(chain, chain[1:]))
    constant += action.cap_bits[0] * _packet_bits(left[0])[0]
    constant += _packet_bits(right[-1])[2] * action.cap_bits[1]
    return AffineValue(coefficient, constant)


def vertical_edges(source: ControlKey, action: ActionKey) -> AffineValue:
    source_exceptions = tuple(
        (item.endpoint, item.atom.previous_word) for item in source.exceptions
    )
    source_left, source_right = boundary_values(
        source.dominant.previous_word, source_exceptions
    )
    action_left, action_right = boundary_values(
        action.dominant_packet, action.exceptions
    )
    dominant = (
        source.dominant.previous_word & action.dominant_packet
    ).bit_count()
    boundary = sum(
        (previous & current).bit_count()
        for previous, current in zip(
            (*source_left, *source_right), (*action_left, *action_right)
        )
    )
    caps = sum(
        previous * current
        for previous, current in zip(source.previous_cap_bits, action.cap_bits)
    )
    return AffineValue(dominant, boundary - 6 * dominant + caps)


def _component_starts(atom: BoundaryDefectAtom) -> int:
    return sum(not role.carries_in for role in atom.carrier_roles)


def frontier_debt(control: ControlKey) -> AffineValue:
    exceptions = tuple((item.endpoint, item.atom) for item in control.exceptions)
    packets = _regular_point_sum(control.dominant, exceptions, _component_starts)
    left = int(control.left_face_role in ("single", "open"))
    return _add(packets, AffineValue(0, left))


def new_faces(target: ControlKey) -> AffineValue:
    return AffineValue(0, 0) if target.cap_mode == "closed" else AffineValue(3, 1)


def certify_counters(
    source: ControlKey, action: ActionKey, target: ControlKey
) -> StableCounterCertificate:
    if (source.size_regime, target.size_regime) != ("stable", "stable"):
        raise ValueError("stable certificates require stable source and target controls")
    edges = _add(horizontal_edges(action), vertical_edges(source, action))
    rank = _add(new_faces(target), frontier_debt(source), _subtract(AffineValue(0, 0), frontier_debt(target)))
    cycles = _subtract(edges, rank)
    return StableCounterCertificate(
        source,
        action,
        target,
        AffineDeltas(
            u=action_u(action),
            cycles=cycles,
            row=AffineValue(0, 1),
            length=AffineValue(0, 0),
        ),
    )


def stable_rule_certificates() -> tuple[StableCounterCertificate, ...]:
    """Return the 19 distinct stable rules, derived from the minimum stable trace."""
    observations = trace_observations(23, residue_two_affine_pattern(23))
    rules = {structural_key(item) for item in observations}
    certificates = tuple(
        certify_counters(source, action, target)
        for source, action, target in sorted(rules, key=repr)
    )
    if len(certificates) != 19:
        raise AssertionError(f"expected 19 stable rules, got {len(certificates)}")
    return certificates


__all__ = [
    "StableCounterCertificate",
    "action_u",
    "boundary_values",
    "certify_counters",
    "frontier_debt",
    "horizontal_edges",
    "new_faces",
    "stable_rule_certificates",
    "vertical_edges",
]
