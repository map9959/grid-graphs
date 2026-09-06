#!/usr/bin/env python3
"""Exact fixed-width defect-gap certificate for residue-two frontiers.

The certificate exhausts the reachable and completable layers at widths 5 and
8.  It makes no claim about any other width.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter
from pathlib import Path

from analysis._paths import analysis_path
from analysis.residue_certificates.residue_two_carrier_grammar import recognize_state
from analysis.residue_certificates.residue_two_local_motif_grammar import (
    grammar_acceptance,
    learn_local_alphabet,
    maximum_face_cut_open_width,
    packet_motif_symbols,
)
from analysis.tiles.tile_grammar import FrontierState, advance_row
from analysis.transport.equality_corridor import (
    EqualityCorridor,
    build_equality_corridor,
    structural_key,
)

SCHEMA = "grid-graphs.residue-two-structural-defect-gap.v1"
WIDTHS = (5, 8)
DEFAULT_OUTPUT = analysis_path("residue_two_structural_defect_gap.json")
CATEGORIES = (
    "support_hole_count",
    "concurrent_packet_carriers",
    "maximum_face_cut_width_gt_1",
    "forbidden_motif_010",
    "forbidden_motif_101",
    "forbidden_motif_121",
    "combined_grammar_rejection",
)


def state_defects(
    state: FrontierState, alphabet: frozenset[tuple[int, ...]]
) -> dict[str, int]:
    """Return positive defect magnitudes, omitting absent categories."""
    recognition = recognize_state(state)
    symbols = packet_motif_symbols(state)
    face_cut_width = maximum_face_cut_open_width(state)
    decisions = grammar_acceptance(state, alphabet)
    values = {
        "support_hole_count": recognition.metrics.support_holes,
        "concurrent_packet_carriers": max(
            recognition.metrics.maximum_concurrent_carriers - 1, 0
        ),
        "maximum_face_cut_width_gt_1": max(face_cut_width - 1, 0),
        "forbidden_motif_010": symbols.count((0, 1, 0)),
        "forbidden_motif_101": symbols.count((1, 0, 1)),
        "forbidden_motif_121": symbols.count((1, 2, 1)),
        "combined_grammar_rejection": int(not decisions["combined"]),
    }
    return {name: value for name, value in values.items() if value}


def _key_json(key: tuple[int, int, tuple[int, ...]]) -> list:
    return [key[0], key[1], list(key[2])]


def _mask(mask: int, width: int) -> str:
    return f"0b{mask:0{width}b}"


def _state_witness(
    corridor: EqualityCorridor,
    key: tuple[int, int, tuple[int, ...]],
    slack: int,
    value: int,
) -> dict:
    row = key[0]
    return {
        "width": corridor.n,
        "row": row,
        "structural_key": _key_json(key),
        "previous_mask_rendered": _mask(key[1], corridor.n),
        "partition": list(key[2]),
        "forward": corridor.forward[row][key],
        "backward": corridor.backward[row][key],
        "minimum": corridor.minimum_weight,
        "reduced_slack": slack,
        "defect_value": value,
    }


def _edge_weight(incoming: FrontierState, mask: int, outgoing: FrontierState) -> int:
    runs = (mask & ~(mask << 1)).bit_count()
    vertical = (incoming.previous_u_mask & mask).bit_count()
    cycles = outgoing.cycle_excess - incoming.cycle_excess
    return mask.bit_count() + 2 * runs - 2 * vertical + 2 * cycles - 1


def _transition_witness(
    corridor: EqualityCorridor,
    incoming_key: tuple[int, int, tuple[int, ...]],
    outgoing_key: tuple[int, int, tuple[int, ...]],
    mask: int,
    weight: int,
    slack: int,
    value: int,
) -> dict:
    row = incoming_key[0]
    return {
        "width": corridor.n,
        "row": row,
        "incoming_structural_key": _key_json(incoming_key),
        "outgoing_structural_key": _key_json(outgoing_key),
        "previous_mask_rendered": _mask(incoming_key[1], corridor.n),
        "row_mask_rendered": _mask(mask, corridor.n),
        "partition": list(outgoing_key[2]),
        "forward": corridor.forward[row][incoming_key],
        "edge_weight": weight,
        "backward": corridor.backward[row + 1][outgoing_key],
        "minimum": corridor.minimum_weight,
        "complete_path_edge_slack": slack,
        "created_defect_value": value,
    }


def _empty_accumulator() -> dict[str, dict]:
    return {
        name: {"slacks": Counter(), "widths": Counter(), "witness_rank": None, "witness": None}
        for name in CATEGORIES
    }


def _record(
    accumulator: dict[str, dict],
    name: str,
    width: int,
    slack: int,
    rank: tuple,
    witness: dict,
) -> None:
    report = accumulator[name]
    report["slacks"][slack] += 1
    report["widths"][width] += 1
    if report["witness_rank"] is None or rank < report["witness_rank"]:
        report["witness_rank"] = rank
        report["witness"] = witness


def _finish(accumulator: dict[str, dict], count_name: str) -> dict:
    result = {}
    for name in CATEGORIES:
        report = accumulator[name]
        if not report["slacks"]:
            continue
        minimum = min(report["slacks"])
        result[name] = {
            count_name: sum(report["slacks"].values()),
            "counts_by_width": {
                str(width): count for width, count in sorted(report["widths"].items())
            },
            "minimum_slack": minimum,
            "counts_by_slack": {
                str(slack): count for slack, count in sorted(report["slacks"].items())
            },
            "witness": report["witness"],
        }
    return result


def build_artifact() -> dict:
    corridors = {width: build_equality_corridor(width) for width in WIDTHS}
    alphabet = learn_local_alphabet(corridors)
    state_reports = _empty_accumulator()
    edge_reports = _empty_accumulator()
    defects_by_width: dict[int, dict[tuple, dict[str, int]]] = {}
    coverage = {}

    for width, corridor in corridors.items():
        cache = {
            key: state_defects(state, alphabet)
            for layer in corridor.layers
            for key, state in layer.items()
        }
        defects_by_width[width] = cache
        completable_states = 0
        for row, layer in enumerate(corridor.layers):
            for key in layer:
                suffix = corridor.backward[row].get(key)
                if suffix is None:
                    continue
                completable_states += 1
                slack = corridor.forward[row][key] + suffix - corridor.minimum_weight
                defects = cache[key]
                if key in corridor.corridor_states[row]:
                    if slack != 0 or defects:
                        raise AssertionError("equality state has positive slack or a structural defect")
                for name, value in defects.items():
                    if slack <= 0:
                        raise AssertionError("observed state defect does not have positive slack")
                    rank = (slack, width, row, key, value)
                    _record(
                        state_reports,
                        name,
                        width,
                        slack,
                        rank,
                        _state_witness(corridor, key, slack, value),
                    )

        completable_edges = 0
        equality_edge_ids = {
            (edge.row, edge.incoming, edge.mask, edge.outgoing)
            for edges in corridor.corridor_edges
            for edge in edges
        }
        for row in range(width):
            for incoming_key, incoming in corridor.layers[row].items():
                incoming_defects = cache[incoming_key]
                for mask in range(1 << width):
                    outgoing = advance_row(incoming, mask)
                    if outgoing is None:
                        continue
                    outgoing_key = structural_key(outgoing)
                    suffix = corridor.backward[row + 1].get(outgoing_key)
                    if suffix is None:
                        continue
                    completable_edges += 1
                    weight = _edge_weight(incoming, mask, outgoing)
                    slack = corridor.forward[row][incoming_key] + weight + suffix - corridor.minimum_weight
                    outgoing_defects = cache[outgoing_key]
                    edge_id = (row, incoming_key, mask, outgoing_key)
                    if edge_id in equality_edge_ids:
                        if slack != 0 or incoming_defects or outgoing_defects:
                            raise AssertionError("equality edge has positive slack or a structural defect")
                    for name, value in outgoing_defects.items():
                        if name in incoming_defects:
                            continue
                        if slack <= 0:
                            raise AssertionError("defect-creating transition does not have positive slack")
                        rank = (slack, width, row, incoming_key, mask, outgoing_key, value)
                        _record(
                            edge_reports,
                            name,
                            width,
                            slack,
                            rank,
                            _transition_witness(
                                corridor, incoming_key, outgoing_key, mask, weight, slack, value
                            ),
                        )

        coverage[str(width)] = {
            "reachable_states": sum(map(len, corridor.layers)),
            "completable_states": completable_states,
            "equality_states": sum(map(len, corridor.corridor_states)),
            "completable_transitions": completable_edges,
            "equality_edges": len(equality_edge_ids),
            "minimum_weight": corridor.minimum_weight,
        }

    states = _finish(state_reports, "states")
    transitions = _finish(edge_reports, "creating_transitions")
    return {
        "schema": SCHEMA,
        "scope": {
            "semantics": "exact-fixed-width-complete-path-defect-gap-certificate",
            "complete_equality_corridors": list(WIDTHS),
            "complete_reachable_and_completable_layers": list(WIDTHS),
            "arbitrary_width_coverage_claimed": False,
        },
        "definitions": {
            "state_reduced_slack": "minimum forward prefix plus minimum accepting suffix minus the width minimum",
            "complete_path_edge_slack": "minimum forward prefix plus exact edge weight plus minimum accepting suffix minus the width minimum",
            "accepting_suffix": "the structural state occurs in the exact backward-distance map",
            "creating_transition": "the category is absent at the incoming state and present at the outgoing state",
            "combined_grammar_rejection": "rejection by carrier_only and local_motifs_only combined; face-cut width is reported separately",
            "previous_mask_rendering": "fixed-width binary, least significant bit is the leftmost row position",
        },
        "coverage": coverage,
        "state_defects": states,
        "transition_created_defects": transitions,
        "absent_categories": {
            "states": sorted(set(CATEGORIES) - set(states)),
            "creating_transitions": sorted(set(CATEGORIES) - set(transitions)),
        },
        "assertions": {
            "all_equality_states_have_no_defects": True,
            "all_equality_edges_have_no_defective_endpoints": True,
            "every_observed_state_defect_has_positive_slack": True,
            "every_observed_created_edge_defect_has_positive_slack": True,
        },
        "limitations": [
            "This exact certificate covers only widths 5 and 8.",
            "It does not establish arbitrary-width, inductive, or theorem-level coverage.",
            "Transition counts include only accepted transitions whose outgoing state has an accepting suffix.",
        ],
        "provenance": {
            "producer": "analysis/residue_certificates/residue_two_structural_defect_gap.py",
            "command": [
                "python3", "-B", "-m",
                                 'analysis.residue_certificates.residue_two_structural_defect_gap',
                "--output", "analysis/residue_two_structural_defect_gap.json",
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
        print(f"exact fixed-width structural defect-gap certificate matches {args.output}")
    else:
        args.output.write_text(rendered)
        print(rendered, end="")


if __name__ == "__main__":
    main()
