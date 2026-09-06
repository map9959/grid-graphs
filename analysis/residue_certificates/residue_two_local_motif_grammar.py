#!/usr/bin/env python3
"""Finite learned local-motif refinement of the residue-two carrier grammar.

The width-three rooted restriction alphabet is learned from every state in the
complete n=5 and n=8 equality corridors.  All claims are finite diagnostics:
the larger widths are fixed traces, and no extrapolation is certified.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter
from pathlib import Path

from analysis._paths import analysis_path
from analysis.patterns.diagonal_patterns import (
    residue_two_affine_pattern,
    residue_two_explicit_pattern,
)
from analysis.residue_certificates.residue_two_carrier_grammar import recognize_state
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

SCHEMA = "grid-graphs.residue-two-local-motif-grammar.v1"
DEFAULT_OUTPUT = analysis_path("residue_two_local_motif_grammar.json")
CORRIDOR_WIDTHS = (5, 8)
FIXED_WIDTHS = (11, 14, 17)
GRAMMARS = ("carrier_only", "local_motifs_only", "combined", "combined_face_cut")


def rooted_restriction(state: FrontierState, slots: tuple[int, ...]) -> tuple[int, ...]:
    """Restrict face slots and canonically root the OUT component at zero."""
    if len(state.partition) == 1:
        return ()
    out = state.partition[0]
    labels = {out: 0}
    result = []
    for slot in slots:
        component = state.partition[slot + 1]
        labels.setdefault(component, len(labels))
        result.append(labels[component])
    return tuple(result)


def packet_motif_symbols(state: FrontierState) -> tuple[tuple[int, ...], ...]:
    """Return rooted restrictions for the consecutive interior triples."""
    if state.n < 5 or state.n % 3 != 2:
        raise ValueError("local motifs require n=3k+2 with k>=1")
    return tuple(
        rooted_restriction(state, tuple(range(1 + 3 * packet, 4 + 3 * packet)))
        for packet in range((state.n - 2) // 3)
    )


def equality_states(corridor: EqualityCorridor) -> list[FrontierState]:
    return [
        corridor.layers[row][key]
        for row, keys in enumerate(corridor.corridor_states)
        for key in keys
    ]


def reachable_states(corridor: EqualityCorridor) -> list[FrontierState]:
    return [state for layer in corridor.layers for state in layer.values()]


def learn_local_alphabet(corridors: dict[int, EqualityCorridor]) -> frozenset[tuple[int, ...]]:
    """Learn the exact union of symbols in the supplied equality corridors."""
    return frozenset(
        symbol
        for corridor in corridors.values()
        for state in equality_states(corridor)
        for symbol in packet_motif_symbols(state)
    )


def all_rooted_triple_symbols() -> tuple[tuple[int, int, int], ...]:
    """Enumerate all 15 canonical restrictions with an implicit rooted OUT."""
    words: list[tuple[int, ...]] = [()]
    for _ in range(3):
        words = [(*word, label) for word in words for label in range(max(word, default=0) + 2)]
    return tuple(words)


def face_cut_open_widths(state: FrontierState) -> tuple[int, ...]:
    """Count non-OUT component hulls crossing each adjacent-face cut."""
    if len(state.partition) == 1:
        return ()
    positions: dict[int, list[int]] = {}
    for slot, component in enumerate(state.partition[1:]):
        if component != state.partition[0]:
            positions.setdefault(component, []).append(slot)
    return tuple(
        sum(slots[0] <= cut < slots[-1] for slots in positions.values())
        for cut in range(state.n - 2)
    )


def maximum_face_cut_open_width(state: FrontierState) -> int:
    return max(face_cut_open_widths(state), default=0)


def grammar_acceptance(
    state: FrontierState, alphabet: frozenset[tuple[int, ...]]
) -> dict[str, bool]:
    carrier = recognize_state(state).accepted
    local = all(symbol in alphabet for symbol in packet_motif_symbols(state))
    combined = carrier and local
    return {
        "carrier_only": carrier,
        "local_motifs_only": local,
        "combined": combined,
        "combined_face_cut": combined and maximum_face_cut_open_width(state) <= 1,
    }


def hull_carrier_local_acceptance(
    state: FrontierState, alphabet: frozenset[tuple[int, ...]]
) -> bool:
    """Allow silent carrier passage while retaining local motifs and hull width one."""
    return (
        all(symbol in alphabet for symbol in packet_motif_symbols(state))
        and maximum_face_cut_open_width(state) <= 1
    )


def _histogram(values) -> dict[str, int]:
    return {str(value): count for value, count in sorted(Counter(values).items())}


def _state_census(
    states: list[FrontierState], alphabet: frozenset[tuple[int, ...]]
) -> dict:
    accepted = Counter()
    combinations = Counter()
    open_widths = []
    excluded_symbols = Counter()
    for state in states:
        decisions = grammar_acceptance(state, alphabet)
        accepted.update(name for name, keep in decisions.items() if keep)
        combinations["+".join(name for name in GRAMMARS if decisions[name]) or "none"] += 1
        open_widths.append(maximum_face_cut_open_width(state))
        excluded_symbols.update(
            symbol for symbol in packet_motif_symbols(state) if symbol not in alphabet
        )
    return {
        "states": len(states),
        "grammars": {
            name: {"accepted": accepted[name], "excluded": len(states) - accepted[name]}
            for name in GRAMMARS
        },
        "acceptance_combinations": dict(sorted(combinations.items())),
        "maximum_face_cut_open_width_histogram": _histogram(open_widths),
        "excluded_local_symbol_occurrences": {
            _symbol_id(symbol): count
            for symbol, count in sorted(excluded_symbols.items())
        },
    }


def _fixed_trace(width: int) -> list[FrontierState]:
    rows = residue_two_affine_pattern(width) if width == 17 else residue_two_explicit_pattern(width)
    state = initial_state(width)
    states = [state]
    for index, row in enumerate(rows):
        state = advance_row(state, row_mask(row))
        if state is None:
            raise AssertionError(f"fixed n={width} trace failed at row {index}")
        states.append(state)
    return states


def _transition_census(
    corridor: EqualityCorridor, alphabet: frozenset[tuple[int, ...]]
) -> dict:
    equality_edges = {
        (row, edge.incoming, edge.mask, edge.outgoing)
        for row, edges in enumerate(corridor.corridor_edges)
        for edge in edges
    }
    counts = {name: Counter() for name in GRAMMARS}
    decision_cache: dict[tuple, dict[str, bool]] = {}

    def decisions(state: FrontierState) -> dict[str, bool]:
        key = structural_key(state)
        if key not in decision_cache:
            decision_cache[key] = grammar_acceptance(state, alphabet)
        return decision_cache[key]

    for row in range(corridor.n):
        for incoming_key, incoming in corridor.layers[row].items():
            incoming_decisions = decisions(incoming)
            for name, keep in incoming_decisions.items():
                if keep:
                    counts[name]["incoming_states"] += 1
            if not any(incoming_decisions.values()):
                continue
            for mask in range(1 << corridor.n):
                outgoing = advance_row(incoming, mask)
                for name, keep in incoming_decisions.items():
                    if keep:
                        counts[name]["masks_attempted"] += 1
                if outgoing is None:
                    continue
                outgoing_key = structural_key(outgoing)
                outgoing_decisions = decisions(outgoing)
                edge_id = (row, incoming_key, mask, outgoing_key)
                for name, keep in incoming_decisions.items():
                    if not keep:
                        continue
                    counts[name]["frontier_accepted_transitions"] += 1
                    field = "staying_in_grammar" if outgoing_decisions[name] else "leaving_grammar"
                    counts[name][field] += 1
                    if edge_id in equality_edges and outgoing_decisions[name]:
                        counts[name]["retained_equality_corridor_edges"] += 1

    return {
        name: {
            **{field: counts[name][field] for field in (
                "incoming_states", "masks_attempted", "frontier_accepted_transitions",
                "staying_in_grammar", "leaving_grammar",
                "retained_equality_corridor_edges",
            )},
            "total_equality_corridor_edges": len(equality_edges),
            "retains_all_equality_edges": counts[name]["retained_equality_corridor_edges"]
            == len(equality_edges),
        }
        for name in GRAMMARS
    }


def _symbol_id(symbol: tuple[int, ...]) -> str:
    return "empty" if not symbol else "".join(map(str, symbol))


def _alphabet_report(
    corridors: dict[int, EqualityCorridor], alphabet: frozenset[tuple[int, ...]]
) -> dict:
    counts = {
        width: Counter(
            symbol
            for state in equality_states(corridor)
            for symbol in packet_motif_symbols(state)
        )
        for width, corridor in corridors.items()
    }
    descriptions = {
        "empty": "empty initial/terminal frontier restriction",
        "000": "three OUT faces",
        "001": "two OUT faces then one component",
        "011": "OUT face then a repeated component",
        "012": "OUT face then two distinct components",
        "100": "one component then two OUT faces",
        "102": "two distinct components separated by OUT",
        "110": "a repeated component then OUT",
        "111": "one component on all three faces",
        "112": "a repeated component then a distinct component",
        "120": "two distinct components then OUT",
        "122": "one component then a distinct repeated component",
        "123": "three distinct non-OUT components",
    }
    allowed = []
    for symbol in sorted(alphabet, key=lambda item: (len(item), item)):
        identifier = _symbol_id(symbol)
        allowed.append({
            "id": identifier,
            "symbol": list(symbol),
            "description": descriptions[identifier],
            "observations": {str(width): counts[width][symbol] for width in CORRIDOR_WIDTHS},
        })
    reasons = {
        "010": "OUT/non-OUT/OUT rooted island; absent from both complete equality corridors",
        "101": "non-OUT/OUT/non-OUT sandwich of one component around OUT; absent from both complete equality corridors",
        "121": "non-OUT ABA sandwich around a distinct component; absent from both complete equality corridors",
    }
    excluded = [
        {"id": _symbol_id(symbol), "symbol": list(symbol), "reason": reasons[_symbol_id(symbol)]}
        for symbol in all_rooted_triple_symbols()
        if symbol not in alphabet
    ]
    return {
        "learning_rule": "union of every rooted packet restriction in every n=5 and n=8 equality-corridor state",
        "allowed": allowed,
        "excluded": excluded,
    }


def build_artifact() -> dict:
    corridors = {width: build_equality_corridor(width) for width in CORRIDOR_WIDTHS}
    alphabet = learn_local_alphabet(corridors)
    sources = {}
    for width, corridor in corridors.items():
        sources[f"n{width}-complete-equality-corridor"] = _state_census(
            equality_states(corridor), alphabet
        )
        sources[f"n{width}-full-structurally-reachable-layers"] = _state_census(
            reachable_states(corridor), alphabet
        )
    for width in FIXED_WIDTHS:
        kind = "near-equality-179-U" if width == 17 else "equality"
        sources[f"n{width}-fixed-{kind}-trace"] = _state_census(
            _fixed_trace(width), alphabet
        )

    return {
        "schema": SCHEMA,
        "scope": {
            "semantics": "finite-learned-structural-refinement-diagnostic-only",
            "complete_training_corridors": list(CORRIDOR_WIDTHS),
            "complete_structurally_reachable_layers": list(CORRIDOR_WIDTHS),
            "fixed_equality_traces": [11, 14],
            "near_equality_control": {"width": 17, "u_count": 179},
            "theorem_or_certificate": False,
            "coverage_beyond_enumerated_states_claimed": False,
        },
        "definitions": {
            "packet_layout": "the left frontier face is separate; consecutive triples of face slots 1..n-2 are packets",
            "local_symbol": "canonical partition restriction to one packet with OUT rooted at zero",
            "carrier_only": "the residue_two_carrier_grammar recognizer",
            "local_motifs_only": "every packet restriction belongs to the learned alphabet",
            "combined": "carrier_only and local_motifs_only",
            "face_cut_open_width": "number of non-OUT component occurrence hulls crossing a cut between adjacent frontier faces",
            "combined_face_cut": "combined and maximum face-cut open width at most one",
            "face_cut_justification": "all 325 states in the complete n=5,n=8 equality training corridors have maximum open width at most one",
        },
        "alphabet": _alphabet_report(corridors, alphabet),
        "sources": sources,
        "row_transitions": {
            str(width): _transition_census(corridor, alphabet)
            for width, corridor in corridors.items()
        },
        "limitations": [
            "The alphabet and face-cut rule are observations learned only from complete n=5 and n=8 equality corridors.",
            "The n=11 and n=14 equality traces and n=17 179-U near-equality trace are single fixed controls.",
            "Retaining all enumerated equality edges is not a proof at another width.",
            "No zero-slack coverage, induction, or unbounded grammar claim is made.",
        ],
        "provenance": {
            "producer": "analysis/residue_certificates/residue_two_local_motif_grammar.py",
            "command": [
                "python3", "-B", "-m",
                                 'analysis.residue_certificates.residue_two_local_motif_grammar',
                "--output", "analysis/residue_two_local_motif_grammar.json",
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
        print(f"finite local-motif grammar diagnostic matches {args.output}")
    else:
        if args.output is not None:
            args.output.write_text(rendered)
        print(rendered, end="")


if __name__ == "__main__":
    main()
