#!/usr/bin/env python3
"""Finite observed transition census for compact residue-two frontiers.

This module reports evidence from the generated affine traces n=17..119 and
the fixed equality controls n=11 and n=14.  It is not an arbitrary-k closure
proof: affine counter formulas are fitted only to the observations sharing a
normalized structural transition and are then checked on those observations.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter, defaultdict
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable

from analysis.patterns.diagonal_patterns import residue_two_affine_pattern, residue_two_explicit_pattern
from analysis.residue_certificates.residue_two_affine_motif_grammar import (
    AFFINE_WIDTHS,
    BoundaryDefectAtom,
    CompactBoundaryDefectFrontier,
    encode_compact_boundary_defect_frontier,
    expand_compact_boundary_defect_frontier,
    replay_trace,
)
from analysis.tiles.tile_grammar import FrontierState, advance_row, row_mask
from analysis._paths import analysis_path


SCHEMA = "grid-graphs.residue-two-compact-transition-census.v1"
FIXED_WIDTHS = (11, 14)
DEFAULT_OUTPUT = analysis_path("residue_two_compact_transition.json")


@dataclass(frozen=True, order=True, slots=True)
class TaggedAtom:
    endpoint: str
    atom: BoundaryDefectAtom


@dataclass(frozen=True, slots=True)
class ControlKey:
    """Width-independent fields of a compact incoming or outgoing state."""

    size_regime: str
    row_phase: int
    cap_mode: str
    previous_cap_bits: tuple[int, int]
    left_face_role: str
    dominant: BoundaryDefectAtom
    exceptions: tuple[TaggedAtom, ...]


@dataclass(frozen=True, slots=True)
class ActionKey:
    """Width-independent dominant-packet encoding of the row being consumed."""

    cap_bits: tuple[int, int]
    dominant_packet: int
    exceptions: tuple[tuple[str, int], ...]


@dataclass(frozen=True, slots=True)
class ExactDeltas:
    u: int
    cycles: int
    row: int
    length: int


@dataclass(frozen=True, slots=True)
class AffineValue:
    packet_coefficient: int
    constant: int

    def at(self, packet_length: int) -> int:
        return self.packet_coefficient * packet_length + self.constant


@dataclass(frozen=True, slots=True)
class AffineDeltas:
    u: AffineValue
    cycles: AffineValue
    row: AffineValue
    length: AffineValue


@dataclass(frozen=True, slots=True)
class TransitionObservation:
    width: int
    row_index: int
    packet_length: int
    source: ControlKey
    action: ActionKey
    target: ControlKey
    deltas: ExactDeltas


def cap_mode(state: FrontierState) -> str:
    """Describe the next row boundary without retaining an absolute index."""
    if state.row_index == 0:
        return "top"
    if state.row_index == state.n:
        return "closed"
    if state.row_index + 1 == state.n:
        return "bottom"
    return "bulk"


def endpoint_tag(index: int, length: int) -> str:
    """Normalize an allowed packet endpoint to L0/L1 or R0..R3."""
    if not 0 <= index < length:
        raise ValueError("packet exception index is outside the word")
    if index < 2:
        return f"L{index}"
    distance = length - 1 - index
    if distance <= 3:
        return f"R{distance}"
    raise ValueError("packet exception is not at an allowed endpoint")


def size_regime(packet_length: int) -> str:
    """Separate finite bases from the stable observed affine regime."""
    if packet_length < 5:
        return "small"
    if packet_length == 5:
        return "base17"
    if packet_length == 6:
        return "base20"
    return "stable"


def control_key(encoded: CompactBoundaryDefectFrontier) -> ControlKey:
    return ControlKey(
        size_regime=size_regime(encoded.word.length),
        row_phase=encoded.row_index % 3,
        cap_mode=cap_mode(expand_compact_boundary_defect_frontier(encoded)),
        previous_cap_bits=encoded.previous_cap_bits,
        left_face_role=encoded.left_face_role,
        dominant=encoded.word.dominant,
        exceptions=tuple(
            TaggedAtom(endpoint_tag(index, encoded.word.length), atom)
            for index, atom in encoded.word.exceptions
        ),
    )


def action_key(row: str) -> ActionKey:
    if len(row) < 5 or len(row) % 3 != 2 or set(row) - {".", "U"}:
        raise ValueError("an action row must have residue-two width over '.' and 'U'")
    packets = tuple(
        sum((bit == "U") << offset for offset, bit in enumerate(row[start : start + 3]))
        for start in range(1, len(row) - 1, 3)
    )
    counts = Counter(packets)
    maximum = max(counts.values())
    dominant = min(packet for packet, count in counts.items() if count == maximum)
    return ActionKey(
        cap_bits=(int(row[0] == "U"), int(row[-1] == "U")),
        dominant_packet=dominant,
        exceptions=tuple(
            (endpoint_tag(index, len(packets)), packet)
            for index, packet in enumerate(packets)
            if packet != dominant
        ),
    )


def observe_transition(
    incoming: FrontierState, row: str, outgoing: FrontierState
) -> TransitionObservation:
    """Normalize one exact edge and verify both compact and direct expansion."""
    source = encode_compact_boundary_defect_frontier(incoming)
    target = encode_compact_boundary_defect_frontier(outgoing)
    if expand_compact_boundary_defect_frontier(source) != incoming:
        raise AssertionError("source compact expansion failed")
    if expand_compact_boundary_defect_frontier(target) != outgoing:
        raise AssertionError("target compact expansion failed")
    if advance_row(incoming, row_mask(row)) != outgoing:
        raise AssertionError("compact transition disagrees with advance_row")
    return TransitionObservation(
        width=incoming.n,
        row_index=incoming.row_index,
        packet_length=source.word.length,
        source=control_key(source),
        action=action_key(row),
        target=control_key(target),
        deltas=ExactDeltas(
            outgoing.u_cost - incoming.u_cost,
            outgoing.cycle_excess - incoming.cycle_excess,
            outgoing.row_index - incoming.row_index,
            target.word.length - source.word.length,
        ),
    )


def trace_observations(width: int, rows: Iterable[str]) -> list[TransitionObservation]:
    materialized = tuple(rows)
    states = replay_trace(materialized)
    return [
        observe_transition(incoming, row, outgoing)
        for incoming, row, outgoing in zip(states, materialized, states[1:])
    ]


def structural_key(observation: TransitionObservation) -> tuple[ControlKey, ActionKey, ControlKey]:
    return observation.source, observation.action, observation.target


def input_key(observation: TransitionObservation) -> tuple[ControlKey, ActionKey]:
    return observation.source, observation.action


def _fit_affine(points: Iterable[tuple[int, int]]) -> AffineValue:
    values = sorted(set(points))
    by_length: dict[int, int] = {}
    for length, value in values:
        if length in by_length and by_length[length] != value:
            raise AssertionError("one packet length has conflicting counter deltas")
        by_length[length] = value
    distinct = sorted(by_length.items())
    if len(distinct) == 1:
        result = AffineValue(0, distinct[0][1])
    else:
        (x0, y0), (x1, y1) = distinct[:2]
        numerator = y1 - y0
        denominator = x1 - x0
        if numerator % denominator:
            raise AssertionError("observed counter delta has no integral affine fit")
        coefficient = numerator // denominator
        result = AffineValue(coefficient, y0 - coefficient * x0)
    if any(result.at(length) != value for length, value in distinct):
        raise AssertionError("observed counter delta is not affine in packet length")
    return result


def fit_deltas(observations: Iterable[TransitionObservation]) -> AffineDeltas:
    values = tuple(observations)
    return AffineDeltas(
        u=_fit_affine((item.packet_length, item.deltas.u) for item in values),
        cycles=_fit_affine((item.packet_length, item.deltas.cycles) for item in values),
        row=_fit_affine((item.packet_length, item.deltas.row) for item in values),
        length=_fit_affine((item.packet_length, item.deltas.length) for item in values),
    )


def _jsonable(value: object) -> object:
    if hasattr(value, "__dataclass_fields__"):
        return {key: _jsonable(item) for key, item in asdict(value).items()}
    if isinstance(value, dict):
        return {key: _jsonable(item) for key, item in value.items()}
    if isinstance(value, tuple):
        return [_jsonable(item) for item in value]
    return value


def _digest(value: object, prefix: str) -> str:
    payload = json.dumps(_jsonable(value), sort_keys=True, separators=(",", ":"))
    return prefix + hashlib.sha256(payload.encode("ascii")).hexdigest()[:16]


def _catalog(observations: list[TransitionObservation]) -> tuple[dict, dict]:
    grouped: dict[tuple[ControlKey, ActionKey, ControlKey], list[TransitionObservation]] = defaultdict(list)
    outputs: dict[tuple[ControlKey, ActionKey], set[ControlKey]] = defaultdict(set)
    for observation in observations:
        grouped[structural_key(observation)].append(observation)
        outputs[input_key(observation)].add(observation.target)
    conflicts = {key: targets for key, targets in outputs.items() if len(targets) != 1}
    conflict_witnesses = []
    for key, targets in conflicts.items():
        witnesses = [item for item in observations if input_key(item) == key]
        target_support = []
        for target in sorted(targets, key=lambda item: _digest(item, "C")):
            matching = [item for item in witnesses if item.target == target]
            target_support.append({
                "target_control_id": _digest(target, "C"),
                "widths": sorted({item.width for item in matching}),
                "representative_row_index": matching[0].row_index,
            })
        conflict_witnesses.append({
            "source_control_id": _digest(key[0], "C"),
            "action_id": _digest(key[1], "A"),
            "target_control_ids": sorted(_digest(target, "C") for target in targets),
            "target_support": target_support,
        })

    catalog = {}
    lookup = {}
    for key, occurrences in grouped.items():
        affine = fit_deltas(occurrences)
        rule = {"source": key[0], "action": key[1], "target": key[2], "affine_deltas": affine}
        identifier = _digest(rule, "R")
        lookup[key] = identifier
        widths = sorted({item.width for item in occurrences})
        catalog[identifier] = {
            **{name: _jsonable(value) for name, value in rule.items()},
            "occurrences": len(occurrences),
            "widths": widths,
            "introduced_at_width": widths[0],
        }
    return catalog, {
        "deterministic": not conflicts,
        "distinct_source_action_pairs": len(outputs),
        "conflicting_source_action_pairs": len(conflicts),
        "determinism_conflict_witnesses": conflict_witnesses,
        "lookup": lookup,
    }


def _ledger(
    observations: list[TransitionObservation],
    lookup: dict[tuple[ControlKey, ActionKey, ControlKey], str],
) -> list[dict]:
    return [
        {
            "width": item.width,
            "row_index": item.row_index,
            "packet_length": item.packet_length,
            "rule_id": lookup[structural_key(item)],
            "source_control_id": _digest(item.source, "C"),
            "action_id": _digest(item.action, "A"),
            "target_control_id": _digest(item.target, "C"),
            "exact_deltas": _jsonable(item.deltas),
        }
        for item in observations
    ]


def build_artifact() -> dict:
    affine_by_width = {
        width: trace_observations(width, residue_two_affine_pattern(width))
        for width in AFFINE_WIDTHS
    }
    affine = [item for width in AFFINE_WIDTHS for item in affine_by_width[width]]
    catalog, diagnostics = _catalog(affine)
    lookup = diagnostics.pop("lookup")

    seen: set[str] = set()
    introductions = {}
    for width in AFFINE_WIDTHS:
        supported = {lookup[structural_key(item)] for item in affine_by_width[width]}
        new = supported - seen
        introductions[str(width)] = sorted(new)
        seen.update(new)
    widths_with_new = [int(width) for width, rules in introductions.items() if rules]
    last_new = max(widths_with_new)

    affine_structures = set(lookup)
    affine_inputs = {input_key(item) for item in affine}
    fixed = {}
    for width in FIXED_WIDTHS:
        observations = trace_observations(width, residue_two_explicit_pattern(width))
        structure_covered = [structural_key(item) in affine_structures for item in observations]
        input_covered = [input_key(item) in affine_inputs for item in observations]
        fixed[str(width)] = {
            "transitions": len(observations),
            "covered_by_affine_control_rules": sum(structure_covered),
            "all_covered_by_affine_control_rules": all(structure_covered),
            "source_action_pairs_covered": sum(input_covered),
            "all_source_action_pairs_covered": all(input_covered),
            "transition_coverage": structure_covered,
        }

    controls = {item.source for item in affine} | {item.target for item in affine}
    return {
        "schema": SCHEMA,
        "scope": {
            "semantics": "finite-observed-evidence-only",
            "affine_generated_widths": list(AFFINE_WIDTHS),
            "fixed_equality_controls": list(FIXED_WIDTHS),
            "arbitrary_k_proof": False,
        },
        "definitions": {
            "control": "finite size regime (small/base17/base20/stable); row phase and semantic cap mode; previous cap bits; left-face role; dominant BoundaryDefectAtom; boundary exceptions tagged L0/L1/R0..R3",
            "action": "current cap bits; dominant three-bit packet integer; boundary packet exceptions tagged L0/L1/R0..R3",
            "excluded_from_control_and_action_keys": ["width", "word length", "absolute row_index", "u_cost", "cycle counters"],
            "affine_deltas": "integer coefficient * packet_length + constant, fitted and checked only on observations of the same source/action/target",
            "determinism": "each observed normalized source-control/action pair has one target control",
        },
        "census": {
            "transitions": len(affine),
            "distinct_controls": len(controls),
            "distinct_actions": len({item.action for item in affine}),
            "distinct_rules": len(catalog),
            **diagnostics,
        },
        "rule_introductions": introductions,
        "stabilization": {
            "last_observed_width_introducing_a_rule": last_new,
            "new_rule_horizon_width_steps": (AFFINE_WIDTHS[-1] - last_new) // 3,
            "no_new_rules_after_last_introduction_through_width": AFFINE_WIDTHS[-1],
            "stabilization_beyond_observed_range_claimed": False,
        },
        "fixed_equality_coverage": fixed,
        "rule_catalog": dict(sorted(catalog.items())),
        "transition_ledger": _ledger(affine, lookup),
        "verification": {
            "transitions_with_compact_source_and_target_expansions_checked": len(affine) + sum(item["transitions"] for item in fixed.values()),
            "advance_row_edges_checked": len(affine) + sum(item["transitions"] for item in fixed.values()),
            "all_checks_passed": True,
        },
        "limitations": [
            "The census contains generated affine traces only for n=17..119.",
            "The n=11 and n=14 controls are single fixed equality traces, not complete equality languages.",
            "A quiet observed horizon is not an induction or an arbitrary-k finite-control proof.",
            "Singleton affine fits use coefficient zero and have no cross-width slope evidence.",
        ],
        "provenance": {
            "producer": "analysis/residue_certificates/residue_two_compact_transition.py",
            "command": ["python3", "-B", "analysis/residue_certificates/residue_two_compact_transition.py", "--output", "analysis/residue_two_compact_transition.json"],
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
        print(f"compact transition census matches {args.output}")
    else:
        if args.output is not None:
            args.output.write_text(rendered)
        print(rendered, end="")


if __name__ == "__main__":
    main()
