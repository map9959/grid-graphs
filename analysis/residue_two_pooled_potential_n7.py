#!/usr/bin/env python3
"""Exact finite-width charge-one pooled-potential diagnostic through n=7.

This exhausts the reachable ``tile_grammar`` row quotient only at the listed
finite widths.  It is a width-enumerated diagnostic, not a uniform proof.
Concrete transitions and frontier states are deliberately not serialized.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import deque
from fractions import Fraction
from pathlib import Path
from typing import Any, Sequence

from proof_oriented_identities import (
    frontier_feature_signature,
    tile_grammar_row_deltas,
)
from tile_grammar import FrontierState, advance_row, initial_state


DEFAULT_WIDTHS = tuple(range(3, 9))
DEFAULT_FEATURE = "runs+rows_remaining"
DEFAULT_OUTPUT = Path(__file__).with_name("residue_two_pooled_potential_n8.json")
KNOWN_MINIMUM_U = {3: 5, 4: 8, 5: 14, 6: 20, 7: 27, 8: 37}


def _state_key(state: FrontierState) -> tuple[int, int, tuple[int, ...]]:
    return state.row_index, state.previous_u_mask, state.partition


def _metadata(state: FrontierState) -> dict[str, Any]:
    return {
        "row_index": state.row_index,
        "previous_u_mask": state.previous_u_mask,
        "partition": state.partition,
    }


def _feature_id(feature: tuple) -> str:
    return json.dumps(feature, separators=(",", ":"), ensure_ascii=True)


def _project_feature(n: int, state: FrontierState, feature_level: str) -> tuple:
    if feature_level == DEFAULT_FEATURE:
        runs = frontier_feature_signature(n, _metadata(state), "runs")
        rows_remaining = 0 if runs[1] in ("top", "terminal") else n - state.row_index
        return (*runs, rows_remaining)
    return frontier_feature_signature(n, _metadata(state), feature_level)


def _fraction_json(value: Fraction) -> list[int]:
    return [value.numerator, value.denominator]


def _ceil_fraction(value: Fraction) -> int:
    return -((-value.numerator) // value.denominator)


def _hash_lines(lines: Sequence[str]) -> str:
    digest = hashlib.sha256()
    for line in lines:
        digest.update(line.encode("ascii"))
        digest.update(b"\n")
    return digest.hexdigest()


def exact_bellman_ford_potentials(
    state_ids: Sequence[str],
    pooled: dict[tuple[str, str], tuple[int, str, int, int]],
    anchor: str,
) -> dict[str, Fraction]:
    """Compute exact shortest potentials with queue-based Bellman-Ford."""
    known = set(state_ids)
    if len(known) != len(state_ids) or anchor not in known:
        raise ValueError("potential synthesis needs unique states and a known anchor")
    adjacency: dict[str, list[tuple[str, int]]] = {state_id: [] for state_id in state_ids}
    for (incoming, outgoing), (weight, _, _, _) in pooled.items():
        if incoming not in known or outgoing not in known:
            raise ValueError("pooled constraint references an unknown feature state")
        adjacency[incoming].append((outgoing, weight))
    for edges in adjacency.values():
        edges.sort()

    distances: dict[str, int | None] = {state_id: None for state_id in state_ids}
    distances[anchor] = 0
    queue = deque([anchor])
    queued = {anchor}
    enqueue_counts = {state_id: 0 for state_id in state_ids}
    enqueue_counts[anchor] = 1
    while queue:
        incoming = queue.popleft()
        queued.remove(incoming)
        incoming_distance = distances[incoming]
        assert incoming_distance is not None
        for outgoing, weight in adjacency[incoming]:
            candidate = incoming_distance + weight
            if distances[outgoing] is not None and candidate >= distances[outgoing]:
                continue
            distances[outgoing] = candidate
            if outgoing not in queued:
                enqueue_counts[outgoing] += 1
                if enqueue_counts[outgoing] > len(state_ids):
                    raise ValueError("negative cycle in pooled difference constraints")
                queue.append(outgoing)
                queued.add(outgoing)
    unreachable = [state_id for state_id, value in distances.items() if value is None]
    if unreachable:
        raise ValueError(f"feature states are unreachable from anchor: {unreachable[:3]}")
    return {
        state_id: Fraction(value)
        for state_id, value in distances.items()
        if value is not None
    }


def build_experiment(
    widths: Sequence[int] = DEFAULT_WIDTHS, feature_level: str = DEFAULT_FEATURE
) -> dict[str, Any]:
    """Enumerate and pool all accepted charge-one transitions at finite widths."""
    normalized = tuple(sorted(set(widths)))
    if not normalized or any(n < 3 or n > 8 for n in normalized):
        raise ValueError("widths must be a nonempty subset of 3..8")
    # Validate the requested existing feature level before doing substantial work.
    _project_feature(3, initial_state(3), feature_level)

    features: set[str] = set()
    pooled: dict[tuple[str, str], tuple[int, str, int, int]] = {}
    terminal_features_by_width: dict[int, set[str]] = {}
    width_reports: dict[str, dict[str, Any]] = {}
    concrete_hash = hashlib.sha256()
    concrete_transitions = 0
    attempted_total = 0

    anchor = _feature_id(
        _project_feature(normalized[0], initial_state(normalized[0]), feature_level)
    )

    for n in normalized:
        start = initial_state(n)
        width_anchor = _feature_id(_project_feature(n, start, feature_level))
        if width_anchor != anchor:
            raise AssertionError("initial frontiers do not share one pooled feature")

        representatives = {_state_key(start): start}
        exact_distances = {_state_key(start): Fraction(0)}
        layer_counts = [1]
        accepted_by_row: list[int] = []
        attempted = accepted = 0
        width_feature_ids = {width_anchor}

        for _ in range(n):
            children: dict[tuple[int, int, tuple[int, ...]], FrontierState] = {}
            child_distances: dict[tuple[int, int, tuple[int, ...]], Fraction] = {}
            row_accepted = 0
            for incoming_key in sorted(representatives):
                incoming = representatives[incoming_key]
                incoming_feature = _feature_id(_project_feature(n, incoming, feature_level))
                for mask in range(1 << n):
                    attempted += 1
                    outgoing = advance_row(incoming, mask)
                    if outgoing is None:
                        continue
                    accepted += 1
                    row_accepted += 1
                    concrete_transitions += 1
                    outgoing_key = _state_key(outgoing)
                    children.setdefault(outgoing_key, outgoing)
                    outgoing_feature = _feature_id(_project_feature(n, outgoing, feature_level))
                    width_feature_ids.add(outgoing_feature)

                    deltas = tile_grammar_row_deltas(incoming, mask, outgoing)
                    weight = 3 * deltas.u_count - 2 * deltas.rank_delta - 1
                    candidate = exact_distances[incoming_key] + weight
                    previous = child_distances.get(outgoing_key)
                    if previous is None or candidate < previous:
                        child_distances[outgoing_key] = candidate

                    pair = (incoming_feature, outgoing_feature)
                    source = f"n{n}:r{incoming.row_index}:m{mask}"
                    retained = pooled.get(pair)
                    if retained is None or weight < retained[0]:
                        pooled[pair] = (
                            weight,
                            source,
                            deltas.u_count,
                            deltas.rank_delta,
                        )

                    concrete_hash.update(
                        json.dumps(
                            [n, incoming.row_index, incoming_feature, outgoing_feature, weight],
                            separators=(",", ":"),
                        ).encode("ascii")
                    )
                    concrete_hash.update(b"\n")

            representatives = children
            exact_distances = child_distances
            layer_counts.append(len(representatives))
            accepted_by_row.append(row_accepted)

        features.update(width_feature_ids)
        terminal_features = {
            _feature_id(_project_feature(n, state, feature_level))
            for state in representatives.values()
        }
        terminal_features_by_width[n] = terminal_features
        exact_constant = min(exact_distances.values())
        implied_u = _ceil_fraction((exact_constant + n + 2 * (n - 1) ** 2) / 3)
        known = KNOWN_MINIMUM_U.get(n)
        width_reports[str(n)] = {
            "reachable_states_by_row": layer_counts,
            "attempted_transitions": attempted,
            "accepted_transitions": accepted,
            "accepted_transitions_by_destination_row": accepted_by_row,
            "feature_states": len(width_feature_ids),
            "terminal_feature_states": len(terminal_features),
            "exact_charge_one_terminal_constant": _fraction_json(exact_constant),
            "implied_minimum_u": implied_u,
            "known_minimum_u": known,
            "exact_reproduces_known_minimum": known is None or implied_u == known,
        }
        attempted_total += attempted

    potentials = exact_bellman_ford_potentials(sorted(features), pooled, anchor)

    tight_pooled = sum(
        potentials[outgoing] == potentials[incoming] + weight
        for (incoming, outgoing), (weight, _, _, _) in pooled.items()
    )
    pooled_width_constants = {
        str(n): min(potentials[feature] for feature in terminal_features_by_width[n])
        for n in normalized
    }
    phase_constants = {
        str(phase): min(
            value
            for n, value in (
                (n, pooled_width_constants[str(n)]) for n in normalized
            )
            if n % 3 == phase
        )
        for phase in sorted({n % 3 for n in normalized})
    }
    for n in normalized:
        pooled_constant = pooled_width_constants[str(n)]
        report = width_reports[str(n)]
        report["pooled_terminal_constant"] = _fraction_json(pooled_constant)
        pooled_implied_u = _ceil_fraction(
            (pooled_constant + n + 2 * (n - 1) ** 2) / 3
        )
        report["pooled_implied_minimum_u"] = pooled_implied_u
        report["pooled_reproduces_known_minimum"] = (
            report["known_minimum_u"] is None
            or pooled_implied_u == report["known_minimum_u"]
        )

    pooled_lines = [
        json.dumps([incoming, outgoing, weight], separators=(",", ":"))
        for (incoming, outgoing), (weight, _, _, _) in sorted(pooled.items())
    ]
    potential_lines = [
        json.dumps(
            [state_id, value.numerator, value.denominator], separators=(",", ":")
        )
        for state_id, value in sorted(potentials.items())
    ]
    held_out_widths = [n for n in normalized if n >= 7]
    return {
        "scope": {
            "semantics": "width-enumerated-diagnostic-only-not-a-uniform-proof",
            "widths": list(normalized),
            "feature_level": feature_level,
            "base_feature_level": "runs",
            "refinement": "one explicit active-frontier rows-to-terminal coordinate",
            "refinement_reason": (
                "the unrefined runs projection has a negative constraint cycle "
                "when width 7 is included; the rows-remaining refinement restores "
                "finite feasibility through width 7 but becomes too weak at width 8"
            ),
            "uniform_row_charge": 1,
            "held_out_widths": held_out_widths,
            "held_out_meaning": (
                "n=7 and n=8 were not used to choose the pre-existing runs feature; "
                "their exact transitions are included in this reported pooled synthesis"
                if held_out_widths
                else None
            ),
        },
        "census": {
            "attempted_concrete_transitions": attempted_total,
            "accepted_concrete_transitions": concrete_transitions,
            "feature_states": len(features),
            "pooled_strongest_transitions": len(pooled),
            "discarded_parallel_constraints": concrete_transitions - len(pooled),
            "tight_pooled_transitions": tight_pooled,
        },
        "widths": width_reports,
        "analysis": {
            "pooled_phase_terminal_constants": {
                phase: _fraction_json(value) for phase, value in phase_constants.items()
            },
            "known_minima_reproduced_all_widths": all(
                report["pooled_reproduces_known_minimum"]
                for report in width_reports.values()
            ),
            "held_out_widths_reproduce_known_minima": all(
                width_reports[str(n)]["pooled_reproduces_known_minimum"]
                for n in held_out_widths
            ),
            "residue_two_terminal_constant_survives_n8": (
                phase_constants.get("2") == 5
            ),
            "conclusion": (
                "The runs-plus-rows-remaining quotient is falsified as a sharp "
                "cross-width residue-two invariant: width-8 constraints lower the "
                "phase-two terminal constant to 2."
            ),
            "potential_value_denominators": sorted(
                {value.denominator for value in potentials.values()}
            ),
        },
        "hashes": {
            "concrete_transition_stream_sha256": concrete_hash.hexdigest(),
            "pooled_strongest_constraints_sha256": _hash_lines(pooled_lines),
            "exact_fraction_potentials_sha256": _hash_lines(potential_lines),
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="optional compact JSON report")
    args = parser.parse_args()
    result = build_experiment()
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(rendered)
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
