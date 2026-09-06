#!/usr/bin/env python3
"""Exact fixed-width first-defect monitor for the silent-hull language.

The monitor keeps a minimum clean prefix until the first frontier outside the
one-hull codec.  It separately checks exact-oracle transition consistency and
the minimum defect-free terminal curvature.  It makes no arbitrary-width or
bounded symbolic-transition claim.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path

from analysis.transport.equality_corridor import (
    EqualityCorridor,
    StateKey,
    _edge,
    build_equality_corridor,
    structural_key,
)
from analysis.residue_certificates.residue_two_n11_grammar_counterexample import ROWS
from analysis.residue_certificates.residue_two_silent_hull_language import (
    classify_silent_hull_frontier,
)
from analysis.residue_certificates.residue_two_stable_topology_certificate import (
    certify_silent_hull_symbolic_transition,
)
from analysis.tiles.tile_grammar import advance_row, initial_state, row_mask
from analysis._paths import analysis_path


SCHEMA = "grid-graphs.residue-two-first-defect-certificate.v1"
DEFAULT_OUTPUT = analysis_path("residue_two_first_defect_certificate.json")
WIDTHS = (5, 8)


@dataclass(frozen=True, slots=True)
class _Defect:
    total: int
    row: int
    incoming: StateKey
    mask: int
    outgoing: StateKey
    prefix: int
    suffix: int
    face_cut_width: int


def _split_mask(mask: int, n: int) -> tuple[tuple[int, int], tuple[int, ...]]:
    return (
        (mask & 1, (mask >> (n - 1)) & 1),
        tuple((mask >> (1 + 3 * packet)) & 7 for packet in range((n - 2) // 3)),
    )


def _key_json(key: StateKey) -> list:
    return [key[0], key[1], list(key[2])]


def _render_mask(mask: int, n: int) -> str:
    return "".join("U" if mask & (1 << column) else "." for column in range(n))


def _prefix_masks(
    predecessors: list[dict[StateKey, tuple[StateKey, int]]], row: int, key: StateKey
) -> list[int]:
    masks = []
    while row:
        key, mask = predecessors[row][key]
        masks.append(mask)
        row -= 1
    masks.reverse()
    return masks


def _suffix_masks(corridor: EqualityCorridor, row: int, key: StateKey) -> list[int]:
    masks = []
    while row < corridor.n:
        incoming = corridor.layers[row][key]
        remaining = corridor.backward[row][key]
        choice = None
        for mask in range(1 << corridor.n):
            outgoing = advance_row(incoming, mask)
            if outgoing is None:
                continue
            outgoing_key = structural_key(outgoing)
            suffix = corridor.backward[row + 1].get(outgoing_key)
            if suffix is None:
                continue
            edge = _edge(row, key, incoming, mask, outgoing)
            if edge.weight + suffix == remaining:
                choice = (mask, outgoing_key)
                break
        if choice is None:
            raise AssertionError("backward distance has no realizing suffix edge")
        mask, key = choice
        masks.append(mask)
        row += 1
    return masks


def _replay(n: int, masks: list[int]) -> tuple[int, int, list[int]]:
    state = initial_state(n)
    first_bad = None
    for row, mask in enumerate(masks, 1):
        state = advance_row(state, mask)
        if state is None:
            raise AssertionError("first-defect witness replay rejected")
        if first_bad is None and not classify_silent_hull_frontier(state).accepted:
            first_bad = row
    if state.partition != (0,):
        raise AssertionError("first-defect witness is not terminally connected")
    curvature = 3 * state.u_cost - 2 * (n - 1) ** 2 - n
    return state.u_cost, curvature, ([] if first_bad is None else [first_bad])


def _witness(corridor: EqualityCorridor, masks: list[int], first_row: int | None) -> dict:
    u_count, curvature, bad_rows = _replay(corridor.n, masks)
    if first_row is None and bad_rows:
        raise AssertionError("defect-free witness contains a codec defect")
    if first_row is not None and bad_rows != [first_row]:
        raise AssertionError("first codec defect row changed during replay")
    return {
        "first_defect_row": first_row,
        "row_masks": [_render_mask(mask, corridor.n) for mask in masks],
        "u_count": u_count,
        "curvature": curvature,
    }


def _monitor_width(n: int) -> dict:
    corridor = build_equality_corridor(n)
    initial_key = next(iter(corridor.layers[0]))
    clean = {initial_key: 0}
    predecessors: list[dict[StateKey, tuple[StateKey, int]]] = [dict() for _ in range(n + 1)]
    first_defect: _Defect | None = None
    oracle_edges = 0

    for row in range(n):
        children: dict[StateKey, int] = {}
        for incoming_key, prefix in clean.items():
            incoming = corridor.layers[row][incoming_key]
            source_decision = classify_silent_hull_frontier(incoming)
            if not source_decision.accepted or source_decision.encoded is None:
                raise AssertionError("clean DP retained an unencodable source")
            for mask in range(1 << n):
                outgoing = advance_row(incoming, mask)
                if outgoing is None:
                    continue
                outgoing_key = structural_key(outgoing)
                suffix = corridor.backward[row + 1].get(outgoing_key)
                if suffix is None:
                    continue
                edge = _edge(row, incoming_key, incoming, mask, outgoing)
                candidate = prefix + edge.weight
                target_decision = classify_silent_hull_frontier(outgoing)
                if not target_decision.accepted:
                    defect = _Defect(
                        candidate + suffix,
                        row + 1,
                        incoming_key,
                        mask,
                        outgoing_key,
                        candidate,
                        suffix,
                        target_decision.maximum_face_cut_width,
                    )
                    if first_defect is None or (
                        defect.total, defect.row, defect.incoming, defect.mask, defect.outgoing
                    ) < (
                        first_defect.total, first_defect.row, first_defect.incoming,
                        first_defect.mask, first_defect.outgoing,
                    ):
                        first_defect = defect
                    continue

                if target_decision.encoded is None:
                    raise AssertionError("accepted codec decision lacks an encoding")
                caps, packets = _split_mask(mask, n)
                try:
                    certify_silent_hull_symbolic_transition(
                        source_decision.encoded, caps, packets, target_decision.encoded
                    )
                except ValueError as error:
                    raise AssertionError(
                        f"bounded transition rejected n={n} row={row} "
                        f"source={incoming_key!r} mask={mask} target={outgoing_key!r}"
                    ) from error
                oracle_edges += 1
                previous = children.get(outgoing_key)
                if previous is None or candidate < previous:
                    children[outgoing_key] = candidate
                    predecessors[row + 1][outgoing_key] = (incoming_key, mask)
        clean = children

    terminal_key = min(clean, key=lambda key: (clean[key], key))
    terminal_masks = _prefix_masks(predecessors, n, terminal_key)
    terminal = _witness(corridor, terminal_masks, None)
    if terminal["curvature"] != clean[terminal_key]:
        raise AssertionError("clean terminal distance disagrees with replay")

    if first_defect is None:
        defect_report = {"status": "absent"}
    else:
        prefix_masks = _prefix_masks(
            predecessors, first_defect.row - 1, first_defect.incoming
        )
        masks = [
            *prefix_masks,
            first_defect.mask,
            *_suffix_masks(corridor, first_defect.row, first_defect.outgoing),
        ]
        witness = _witness(corridor, masks, first_defect.row)
        if witness["curvature"] != first_defect.total:
            raise AssertionError("first-defect distance disagrees with replay")
        defect_report = {
            "status": "present",
            "minimum_complete_path_curvature": first_defect.total,
            "gap_above_width_minimum": first_defect.total - corridor.minimum_weight,
            "first_row": first_defect.row,
            "incoming_structural_key": _key_json(first_defect.incoming),
            "outgoing_structural_key": _key_json(first_defect.outgoing),
            "maximum_face_cut_width": first_defect.face_cut_width,
            "prefix_weight_through_defect_edge": first_defect.prefix,
            "minimum_suffix_weight": first_defect.suffix,
            "witness": witness,
        }

    return {
        "minimum_unrestricted_curvature": corridor.minimum_weight,
        "minimum_unrestricted_u": corridor.minimum_u,
        "first_state_codec_defect": defect_report,
        "transition_closure_defect": {
            "status": "absent",
            "checked_codec_valid_completable_edges": oracle_edges,
            "interpretation": "bounded streaming topology and local counter certificate",
        },
        "defect_free_terminal": {
            "minimum_complete_path_curvature": terminal["curvature"],
            "meets_terminal_constant_five": terminal["curvature"] >= 5,
            "witness": terminal,
        },
    }


def _n11_silent_control() -> dict:
    state = initial_state(11)
    silent_rows = []
    for row, rendered in enumerate(ROWS, 1):
        incoming_decision = classify_silent_hull_frontier(state)
        outgoing = advance_row(state, row_mask(rendered))
        if outgoing is None:
            raise AssertionError("n11 silent control rejected")
        outgoing_decision = classify_silent_hull_frontier(outgoing)
        if not incoming_decision.accepted or not outgoing_decision.accepted:
            raise AssertionError("n11 silent control left the one-hull codec")
        if incoming_decision.encoded is None or outgoing_decision.encoded is None:
            raise AssertionError("n11 accepted codec decision lacks an encoding")
        caps, packets = _split_mask(row_mask(rendered), 11)
        certify_silent_hull_symbolic_transition(
            incoming_decision.encoded, caps, packets, outgoing_decision.encoded
        )
        if any(atom.silent_carry for atom in outgoing_decision.encoded.atoms):
            silent_rows.append(row)
        state = outgoing
    return {
        "selection": "one fixed equality witness, not complete n11 coverage",
        "all_frontiers_codec_valid": True,
        "all_bounded_symbolic_transitions_valid": True,
        "silent_rows": silent_rows,
    }


def build_artifact() -> dict:
    widths = {str(n): _monitor_width(n) for n in WIDTHS}
    if widths["8"]["first_state_codec_defect"].get("gap_above_width_minimum") != 3:
        raise AssertionError("n8 first codec defect no longer has gap three")
    return {
        "schema": SCHEMA,
        "scope": {
            "semantics": "exact-fixed-width-first-defect-complete-path-monitor",
            "widths": list(WIDTHS),
            "transition_relation": "bounded-streaming-topology-and-local-counters",
            "arbitrary_width_coverage_claimed": False,
            "bounded_symbolic_transition_soundness_proved_for_monitored_edges": True,
            "arbitrary_word_transition_closure_claimed": False,
            "universal_terminal_bound_claimed": False,
        },
        "definitions": {
            "state_codec_defect": "first frontier with face-cut occurrence-hull width greater than one",
            "transition_closure_defect": "codec-valid exact edge rejected by the selected transition relation",
            "defect_free_terminal": "minimum connected complete path that remains codec-valid",
            "charged_curvature": "3|U|-2(n-1)^2-n",
        },
        "widths": widths,
        "n11_silent_control": _n11_silent_control(),
        "limitations": [
            "Complete path monitoring is proved only at widths 5 and 8.",
            "The monitor enumerates exact edges with advance_row, but each retained codec-valid edge is independently certified by the bounded streaming product.",
            "No theorem yet enumerates every admissible arbitrary-width source/action word or proves that its successor remains in the codec.",
            "The n11 control is one path and does not establish complete n11 coverage.",
            "The fixed-width terminal minima do not imply an arbitrary-width terminal bound.",
        ],
        "provenance": {
            "producer": "analysis/residue_certificates/residue_two_first_defect_certificate.py",
            "command": [
                "python3", "-B", "analysis/residue_certificates/residue_two_first_defect_certificate.py",
                "--output", "analysis/residue_two_first_defect_certificate.json",
            ],
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    rendered = json.dumps(build_artifact(), indent=2, sort_keys=True) + "\n"
    if args.check:
        if not args.output.exists() or args.output.read_text() != rendered:
            raise SystemExit(f"stale or missing artifact: {args.output}")
        print(f"first-defect certificate matches {args.output}")
    else:
        args.output.write_text(rendered)
        print(f"wrote {args.output}")


if __name__ == "__main__":
    main()
