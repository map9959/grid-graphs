#!/usr/bin/env python3
"""Exact n=11 equality counterexample to contiguous carrier support coverage."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from residue_two_carrier_grammar import recognize_state
from residue_two_local_motif_grammar import (
    all_rooted_triple_symbols,
    hull_carrier_local_acceptance,
    maximum_face_cut_open_width,
    packet_motif_symbols,
)
from tile_grammar import advance_row, initial_state, row_mask


SCHEMA = "grid-graphs.residue-two-n11-grammar-counterexample.v1"
DEFAULT_OUTPUT = Path(__file__).with_name("residue_two_n11_grammar_counterexample.json")
ROWS = (
    ".U.......U.",
    ".UUUUUUUUU.",
    ".UU.UU.UUU.",
    ".UU.UUUU.U.",
    ".UU.U.UUUU.",
    ".UU.UUU.UU.",
    ".UU.UUU.UU.",
    ".UUUU.U.UU.",
    "UU.UUUU.UU.",
    "UUUUUUUUUUU",
    "...........",
)
FORBIDDEN_MOTIFS = {(0, 1, 0), (1, 0, 1), (1, 2, 1)}
LOCAL_ALPHABET = frozenset({()} | (set(all_rooted_triple_symbols()) - FORBIDDEN_MOTIFS))


def build_artifact() -> dict:
    n = len(ROWS)
    state = initial_state(n)
    states = []
    for row_index, row in enumerate(ROWS, 1):
        outgoing = advance_row(state, row_mask(row))
        if outgoing is None:
            raise AssertionError(f"counterexample seals a component at row {row_index}")
        state = outgoing
        recognition = recognize_state(state)
        motifs = packet_motif_symbols(state)
        states.append(
            {
                "row": row_index,
                "previous_row": row,
                "partition": list(state.partition),
                "carrier_accepted": recognition.accepted,
                "support_holes": [
                    {
                        "component": item.component,
                        "occupied_groups": list(item.occupied_groups),
                        "missing_groups": list(item.missing_groups),
                    }
                    for item in recognition.support_holes
                ],
                "concurrent_packet_carriers": [
                    {
                        "cut": item.cut,
                        "components": list(item.components),
                    }
                    for item in recognition.concurrent_carriers
                ],
                "packet_motifs": [list(item) for item in motifs],
                "forbidden_motifs": [
                    list(item) for item in motifs if item in FORBIDDEN_MOTIFS
                ],
                "maximum_face_cut_open_width": maximum_face_cut_open_width(state),
                "hull_carrier_local_accepted": hull_carrier_local_acceptance(
                    state, LOCAL_ALPHABET
                ),
            }
        )

    u_count = sum(row.count("U") for row in ROWS)
    rank = (n - 1) ** 2
    curvature = 3 * u_count - 2 * rank - n
    rejected = [item for item in states if not item["carrier_accepted"]]
    if state.partition != (0,) or u_count != 72 or curvature != 5:
        raise AssertionError("counterexample is not a connected curvature-five n=11 path")
    if [item["row"] for item in rejected] != [8]:
        raise AssertionError("counterexample must leave the carrier grammar only at row 8")
    if any(item["forbidden_motifs"] for item in states):
        raise AssertionError("counterexample should retain the learned local alphabet")
    if any(item["concurrent_packet_carriers"] for item in states):
        raise AssertionError("counterexample should retain one packet carrier per cut")
    if max(item["maximum_face_cut_open_width"] for item in states) != 1:
        raise AssertionError("counterexample should retain face-cut width one")
    if not all(item["hull_carrier_local_accepted"] for item in states):
        raise AssertionError("counterexample should remain in the widened hull-carrier language")

    return {
        "schema": SCHEMA,
        "scope": {
            "semantics": "exact-counterexample-to-contiguous-support-coverage",
            "width": n,
            "u_count": u_count,
            "charged_curvature": curvature,
            "global_optimality_source": "known exact n=11 minimum U=72",
            "arbitrary_width_claimed": False,
        },
        "pattern": list(ROWS),
        "states": states,
        "failure": {
            "row": 8,
            "kind": "support_hole",
            "component": 3,
            "occupied_groups": [1, 3],
            "missing_groups": [2],
            "repaired_by_next_row": True,
        },
        "surviving_restrictions": {
            "all_packet_motifs_in_n5_n8_alphabet": True,
            "no_concurrent_packet_carriers": True,
            "maximum_face_cut_open_width": 1,
            "all_states_in_hull_carrier_local_language": True,
        },
        "exact_search": {
            "engine": "src/bin/search_n17_frontier_pruned.rs",
            "command": [
                "cargo", "run", "--release", "--bin", "search_n17_frontier_pruned", "--",
                "--n", "11", "--u-count", "72", "--grammar-violation-query",
                "--grammar-violation-kind", "support-hole",
            ],
            "minimum_good_u": 72,
            "minimum_bad_u": 72,
            "peak_product_states": 191615,
            "generated_transitions": 20631703,
        },
        "conclusion": (
            "Zero-slack equality paths are not covered by contiguous packet-group "
            "support. A corrected carrier language must permit a live hull carrier "
            "to pass silently through an unoccupied packet."
        ),
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
        print(f"n=11 grammar counterexample matches {args.output}")
    else:
        args.output.write_text(rendered)
        print(rendered, end="")


if __name__ == "__main__":
    main()
