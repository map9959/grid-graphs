#!/usr/bin/env python3
"""Exact finite certificate for the silent-hull row-packet language controls."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from analysis._paths import analysis_path
from analysis.residue_certificates.residue_two_cap_merge_potential import (
    _difference_certificate,
)
from analysis.residue_certificates.residue_two_n11_grammar_counterexample import ROWS
from analysis.residue_certificates.residue_two_persistent_debt_certificate import (
    lift_corridor,
    lift_fixed_path,
)
from analysis.residue_certificates.residue_two_silent_hull_language import (
    encode_silent_hull_frontier,
    finite_structural_atom_alphabet,
)
from analysis.residue_certificates.residue_two_stable_topology_certificate import (
    certify_silent_hull_symbolic_transition,
)
from analysis.tiles.tile_grammar import advance_row, initial_state, row_mask
from analysis.transport.equality_corridor import build_equality_corridor

SCHEMA = "grid-graphs.residue-two-silent-hull-certificate.v1"
DEFAULT_OUTPUT = analysis_path("residue_two_silent_hull_certificate.json")


def _split_mask(mask: int, n: int) -> tuple[tuple[int, int], tuple[int, ...]]:
    return (
        (mask & 1, (mask >> (n - 1)) & 1),
        tuple((mask >> (1 + 3 * packet)) & 7 for packet in range((n - 2) // 3)),
    )


def _corridor_coverage(n: int) -> dict:
    corridor = build_equality_corridor(n)
    states = 0
    silent_states = 0
    for row, keys in enumerate(corridor.corridor_states):
        for key in keys:
            encoded = encode_silent_hull_frontier(corridor.layers[row][key])
            states += 1
            silent_states += any(atom.silent_carry for atom in encoded.atoms)
    transitions = 0
    for edges in corridor.corridor_edges:
        for edge in edges:
            incoming = corridor.layers[edge.row][edge.incoming]
            outgoing = advance_row(incoming, edge.mask)
            if outgoing is None:
                raise AssertionError("equality edge has no exact successor")
            caps, packets = _split_mask(edge.mask, n)
            counters = certify_silent_hull_symbolic_transition(
                encode_silent_hull_frontier(incoming),
                caps,
                packets,
                encode_silent_hull_frontier(outgoing),
            )
            if counters.weight != edge.weight or counters.cycles != edge.d_cycles:
                raise AssertionError("affine counters disagree with an equality edge")
            transitions += 1
    return {
        "corridor_states": states,
        "states_with_silent_atoms": silent_states,
        "corridor_transitions": transitions,
        "all_states_encoded_losslessly": True,
        "all_transition_counters_exact": True,
    }


def _n11_coverage() -> dict:
    state = initial_state(11)
    silent_rows = []
    transitions = 0
    for row_number, row in enumerate(ROWS, 1):
        outgoing = advance_row(state, row_mask(row))
        if outgoing is None:
            raise AssertionError("n11 silent witness became invalid")
        source = encode_silent_hull_frontier(state)
        target = encode_silent_hull_frontier(outgoing)
        caps, packets = _split_mask(row_mask(row), 11)
        certify_silent_hull_symbolic_transition(source, caps, packets, target)
        if any(atom.silent_carry for atom in target.atoms):
            silent_rows.append(row_number)
        transitions += 1
        state = outgoing
    if silent_rows != [8]:
        raise AssertionError("n11 silent passage is not isolated at row 8")
    return {
        "selection": "one exact equality witness, not complete n11 coverage",
        "transitions": transitions,
        "silent_carrier_rows": silent_rows,
        "all_transition_counters_exact": True,
    }


def _min_plus_certificate() -> dict:
    complete = [lift_corridor(n) for n in (5, 8)]
    silent = lift_fixed_path(11, list(ROWS), "n11-silent")
    anchors = {silent["features"][0]: 0, silent["features"][-1]: -5}
    for source in complete:
        anchors[source["initial"]] = 0
        anchors.update({terminal: -5 for terminal in source["terminals"]})
    certificate = _difference_certificate(
        [
            *(edge for source in complete for edge in source["transitions"]),
            *silent["transitions"],
        ],
        anchors,
    )
    if set(certificate["slack_histogram"]) != {"0"}:
        raise AssertionError("silent-hull finite certificate is not tight")
    return {
        **certificate,
        "terminal_constant": 5,
        "potential_convention": "weight + Phi(target) - Phi(source) >= 0",
        "initial_potential": 0,
        "terminal_potential": -5,
    }


def build_artifact() -> dict:
    return {
        "schema": SCHEMA,
        "scope": {
            "width_independent_exact_result": (
                "lossless finite-control/affine-counter encoding and transition "
                "soundness conditional on face-cut occurrence-hull width at most one"
            ),
            "complete_equality_transition_widths": [5, 8],
            "fixed_witness_widths": [11],
            "arbitrary_width_K_le_2_coverage_proved": False,
            "bounded_symbolic_transition_soundness_proved": True,
            "arbitrary_word_transition_closure_proved": False,
            "universal_terminal_bound_proved": False,
        },
        "language": {
            "finite_atom_alphabet_size": len(finite_structural_atom_alphabet()),
            "finite_control": [
                "left cap/face mode",
                "one active hull carrier",
                "finite rooted packet atom including silent passage",
            ],
            "affine_counters": [
                "packet length",
                "fresh component count",
                "U cost",
                "horizontal and vertical edges",
                "rank and cycle deltas",
            ],
            "conditional_coverage_lemma": (
                "Every n=3k+2 frontier with maximum face-cut occurrence-hull "
                "width at most one has an exact silent-hull encoding."
            ),
            "transition_soundness": (
                "A bounded streaming product checks every admitted source/action/target "
                "word without advance_row; rank, cycle, and charged-weight counters are exact local sums."
            ),
        },
        "complete_finite_coverage": {
            str(n): _corridor_coverage(n) for n in (5, 8)
        },
        "n11_silent_gap": _n11_coverage(),
        "integer_min_plus_certificate": _min_plus_certificate(),
        "uncovered_exact_lemma": {
            "statement": (
                "Every frontier on every hypothetical connected residue-two path "
                "with terminal charged curvature K<=2 has face-cut occurrence-hull "
                "width at most one, or belongs to a specified finite extension."
            ),
            "status": "open",
            "consequence": (
                "Coverage and transition closure are necessary but not sufficient: "
                "a noncircular minimum accepting weight or terminal-control bound is also required."
            ),
            "transition_sublemma": (
                "Prove that every admissible arbitrary-width codec source/action has a "
                "successor still represented by the language; the bounded certifier already "
                "proves soundness of each proposed source/action/target word."
            ),
            "terminal_sublemma": (
                "Prove independently of cumulative U, K, or the target formula that every "
                "accepting symbolic terminal has minimum accumulated weight at least five."
            ),
        },
        "limitations": [
            "Complete equality coverage is proved only at n=5 and n=8.",
            "The n=11 result covers one exact equality witness containing the silent gap.",
            "Transition soundness does not imply that every K<=2 path enters the language.",
            "Bounded transition soundness is proved, but existence and codec closure for every arbitrary source/action remain open.",
            "The integer potential is synthesized only on the declared complete and fixed finite sources.",
            "The finite terminal anchors do not constitute an arbitrary-width terminal theorem.",
        ],
        "provenance": {
            "producer": "analysis/residue_certificates/residue_two_silent_hull_certificate.py",
            "command": [
                "python3",
                "-B",
                "-m",
                'analysis.residue_certificates.residue_two_silent_hull_certificate',
                "--output",
                "analysis/residue_two_silent_hull_certificate.json",
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
        print(f"silent-hull certificate matches {args.output}")
    else:
        args.output.write_text(rendered)
        print(f"wrote {args.output}")


if __name__ == "__main__":
    main()
