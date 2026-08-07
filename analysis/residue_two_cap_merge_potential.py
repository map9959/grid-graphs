#!/usr/bin/env python3
"""Exact cap/merge/branch difference-constraint experiments.

The complete training source consists only of equality-corridor edges at n=5,8.
Fixed n=11,14 paths and the affine n=17 path are extension controls, not source
coverage.  Every checked edge uses weight + Phi(out) - Phi(in) >= 0.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter, defaultdict
from dataclasses import asdict, dataclass
from pathlib import Path

from diagonal_patterns import residue_two_affine_pattern, residue_two_explicit_pattern
from equality_corridor import EqualityCorridor, build_equality_corridor
from proof_oriented_identities import tile_grammar_row_deltas
from residue_two_attachment_history import build_analysis as build_attachment_history
from residue_two_attachment_skeleton import linear_frontier_metric
from tile_grammar import FrontierState, advance_row, initial_state, row_mask


HERE = Path(__file__).resolve().parent
DEFAULT_OUTPUT = HERE / "residue_two_cap_merge_potential.json"
SCHEMA = "grid-graphs.residue-two-cap-merge-potential.v1"
Feature = tuple[str, int, int, int, int, int]


@dataclass(frozen=True, slots=True)
class ProjectedTransition:
    incoming: Feature
    outgoing: Feature
    weight: int
    source: str


def cap_phase(n: int, row: int) -> str:
    if row == 0:
        return "top"
    if row == n:
        return "terminal"
    remaining = n - row
    if remaining <= 2:
        return f"bottom-{remaining}"
    return f"bulk-{row % 3}"


def _debt(partition: tuple[int, ...]) -> int:
    return linear_frontier_metric(partition)["attachment_debt"]


def corridor_merge_capacity(corridor: EqualityCorridor) -> list[dict[tuple, int]]:
    """Maximize cumulative positive debt reduction over an equality suffix."""
    capacity: list[dict[tuple, int]] = [{} for _ in range(corridor.n + 1)]
    capacity[corridor.n] = {key: 0 for key in corridor.corridor_states[corridor.n]}
    for row in range(corridor.n - 1, -1, -1):
        for edge in corridor.corridor_edges[row]:
            reduction = max(0, _debt(edge.incoming[2]) - _debt(edge.outgoing[2]))
            candidate = reduction + capacity[row + 1][edge.outgoing]
            capacity[row][edge.incoming] = max(
                capacity[row].get(edge.incoming, -1), candidate
            )
        if set(capacity[row]) != corridor.corridor_states[row]:
            raise AssertionError("merge capacity does not cover an equality layer")
    return capacity


def feature(n: int, state: FrontierState, remaining_merge_capacity: int) -> Feature:
    metric = linear_frontier_metric(state.partition)
    active_faces = n - 1 if 0 < state.row_index < n else 0
    out = state.partition[0]
    return (
        cap_phase(n, state.row_index),
        active_faces - metric["attachment_debt"],
        remaining_merge_capacity - metric["attachment_debt"],
        state.previous_u_mask.bit_count(),
        sum(label == out for label in state.partition[1:]),
        metric["branch_cost"],
    )


def _path_source(n: int, rows: list[str] | tuple[str, ...], name: str) -> dict:
    state = initial_state(n)
    states = [state]
    weights = []
    for row in rows:
        outgoing = advance_row(state, row_mask(row))
        if outgoing is None:
            raise AssertionError(f"{name} is rejected")
        delta = tile_grammar_row_deltas(state, row_mask(row), outgoing)
        weights.append(3 * delta.u_count - 2 * delta.rank_delta - 1)
        states.append(outgoing)
        state = outgoing
    capacity = [0] * (n + 1)
    for row in range(n - 1, -1, -1):
        capacity[row] = capacity[row + 1] + max(
            0, _debt(states[row].partition) - _debt(states[row + 1].partition)
        )
    features = [feature(n, state, capacity[index]) for index, state in enumerate(states)]
    return {
        "name": name,
        "n": n,
        "states": states,
        "features": features,
        "weights": weights,
        "total_weight": sum(weights),
        "transitions": [
            ProjectedTransition(features[index], features[index + 1], weight, name)
            for index, weight in enumerate(weights)
        ],
    }


def _corridor_source(n: int) -> dict:
    corridor = build_equality_corridor(n)
    capacity = corridor_merge_capacity(corridor)
    features = {}
    potential_values: dict[Feature, set[int]] = defaultdict(set)
    for row, keys in enumerate(corridor.corridor_states):
        for key in keys:
            projected = feature(n, corridor.layers[row][key], capacity[row][key])
            features[key] = projected
            potential_values[projected].add(-corridor.forward[row][key])
    collisions = {
        repr(key): sorted(values)
        for key, values in potential_values.items()
        if len(values) > 1
    }
    if collisions:
        raise AssertionError("full feature has incompatible equality potentials")
    transitions = [
        ProjectedTransition(
            features[edge.incoming], features[edge.outgoing], edge.weight, f"n{n}-complete"
        )
        for edges in corridor.corridor_edges
        for edge in edges
    ]
    initial_key = next(iter(corridor.corridor_states[0]))
    terminals = {
        features[key] for key in corridor.corridor_states[n]
    }
    return {
        "name": f"n{n}-complete",
        "n": n,
        "corridor": corridor,
        "features": set(potential_values),
        "potentials": {key: next(iter(values)) for key, values in potential_values.items()},
        "transitions": transitions,
        "initial": features[initial_key],
        "terminals": terminals,
    }


def _feature_id(value: Feature) -> str:
    return json.dumps(value, separators=(",", ":"))


def _difference_certificate(
    transitions: list[ProjectedTransition], anchors: dict[Feature, int]
) -> dict:
    """Solve exact integer difference constraints with fixed feature anchors."""
    zero = "__ZERO__"
    vertices: set[Feature | str] = {zero}
    edges: list[tuple[Feature | str, Feature | str, int]] = []
    for item in transitions:
        vertices.update((item.incoming, item.outgoing))
        # Phi(in)-Phi(out) <= weight.
        edges.append((item.outgoing, item.incoming, item.weight))
    for state, value in anchors.items():
        vertices.add(state)
        edges.append((zero, state, value))
        edges.append((state, zero, -value))

    ordered_edges = sorted(edges, key=repr)
    distances = {vertex: 0 for vertex in vertices}
    for iteration in range(len(vertices)):
        changed = False
        for incoming, outgoing, weight in ordered_edges:
            candidate = distances[incoming] + weight
            if candidate < distances[outgoing]:
                distances[outgoing] = candidate
                changed = True
        if not changed:
            break
        if iteration + 1 == len(vertices):
            raise AssertionError("projected difference constraints have a negative cycle")
    shift = distances[zero]
    potentials = {
        state: distances[state] - shift for state in vertices if state != zero
    }
    if any(potentials[state] != value for state, value in anchors.items()):
        raise AssertionError("fixed potential anchor was not met")

    slacks = Counter()
    by_source = defaultdict(Counter)
    for item in transitions:
        slack = item.weight + potentials[item.outgoing] - potentials[item.incoming]
        if slack < 0:
            raise AssertionError("synthesized potential violates a transition")
        slacks[slack] += 1
        by_source[item.source][slack] += 1
    return {
        "features": len(potentials),
        "concrete_transitions": len(transitions),
        "distinct_constraints": len(
            {(item.incoming, item.outgoing, item.weight) for item in transitions}
        ),
        "potential_range": [min(potentials.values()), max(potentials.values())],
        "slack_histogram": {str(k): v for k, v in sorted(slacks.items())},
        "slack_by_source": {
            source: {str(k): v for k, v in sorted(values.items())}
            for source, values in sorted(by_source.items())
        },
        "potentials": {
            _feature_id(state): value for state, value in sorted(potentials.items(), key=repr)
        },
    }


def _ablation_collisions(sources: list[dict]) -> dict:
    fields = (
        "cap_phase",
        "component_deficit",
        "merge_capacity_surplus",
        "row_u_count",
        "out_face_count",
        "branch_cost",
    )
    result = {}
    for omitted in fields:
        index = fields.index(omitted)
        groups: dict[tuple, set[int]] = defaultdict(set)
        for source in sources:
            for state, value in source["potentials"].items():
                reduced = (*state[:index], *state[index + 1 :])
                groups[reduced].add(value)
        collisions = [values for values in groups.values() if len(values) > 1]
        result[f"without_{omitted}"] = {
            "feature_states": len(groups),
            "incompatible_groups": len(collisions),
            "maximum_values_in_group": max(map(len, collisions), default=1),
        }
    return result


def _terminal_debt_control() -> dict:
    history = build_attachment_history()
    survivors = history["terminal_178"]["states"]
    deficits = Counter(
        item["rooted_debt"] - item["budgeted_merge_capacity"] for item in survivors
    )
    positive = history["witness_179_suffix"]
    positive_deficit = positive["rooted_debt"] - positive["budgeted_merge_capacity"]
    if min(deficits) <= 0 or positive_deficit != 0:
        raise AssertionError("terminal unpayable-debt separation changed")
    return {
        "definition": "unpayable_debt=max(rooted_debt-remaining_independent_merge_capacity,0)",
        "u178_survivor_deficit_histogram": {
            str(value): count for value, count in sorted(deficits.items())
        },
        "u178_all_positive": True,
        "u179_positive_control_deficit": positive_deficit,
        "scope": "exact final-two-cell n17 artifacts only",
    }


def build_artifact() -> dict:
    complete = [_corridor_source(n) for n in (5, 8)]
    training_transitions = [
        item for source in complete for item in source["transitions"]
    ]
    anchors = {}
    for source in complete:
        anchors[source["initial"]] = 0
        anchors.update({terminal: -5 for terminal in source["terminals"]})
    training = _difference_certificate(training_transitions, anchors)
    if set(training["slack_histogram"]) != {"0"}:
        raise AssertionError("equality training constraints are not all tight")

    fixed = [
        _path_source(11, residue_two_explicit_pattern(11), "n11-fixed"),
        _path_source(14, residue_two_explicit_pattern(14), "n14-fixed"),
    ]
    training_features = set().union(*(source["features"] for source in complete))
    heldout = {}
    for source in fixed:
        known_states = sum(value in training_features for value in source["features"])
        known_edges = sum(
            item.incoming in training_features and item.outgoing in training_features
            for item in source["transitions"]
        )
        heldout[source["name"]] = {
            "total_weight": source["total_weight"],
            "states": len(source["features"]),
            "states_known_to_training": known_states,
            "edges_fully_known_to_training": known_edges,
            "direct_heldout_certificate": known_edges == len(source["transitions"]),
        }
    fixed_transitions = [item for source in fixed for item in source["transitions"]]
    fixed_extension = _difference_certificate(
        [*training_transitions, *fixed_transitions], anchors
    )

    n17 = _path_source(17, residue_two_affine_pattern(17), "n17-affine-179")
    n17_extension = _difference_certificate(
        [*training_transitions, *fixed_transitions, *n17["transitions"]], anchors
    )
    n17_terminal = n17["features"][-1]
    terminal_training_potential = training["potentials"].get(_feature_id(n17_terminal))
    if terminal_training_potential != -5:
        raise AssertionError("n17 accepted terminal is not a trained constant-five feature")

    return {
        "schema": SCHEMA,
        "scope": {
            "complete_transition_sources": [5, 8],
            "fixed_path_extension_controls": [11, 14],
            "surplus_path_extension_control": {"n": 17, "u_count": 179},
            "n17_failed_terminal_control": "20 committed u178 states at step 287",
            "arbitrary_width_coverage_claimed": False,
        },
        "inequality": "weight + Phi(out) - Phi(in) >= 0",
        "feature": {
            "fields": [
                "cap_phase",
                "active_faces_minus_attachment_debt",
                "remaining_merge_capacity_minus_attachment_debt",
                "previous_row_u_count",
                "out_face_count",
                "branch_cost",
            ],
            "remaining_merge_capacity": (
                "maximum cumulative positive attachment-debt reduction over a retained "
                "equality suffix; fixed paths use their unique displayed suffix"
            ),
            "silent_carrier_policy": (
                "no contiguous-support bit is present; branch cost retains separated "
                "occurrence runs across silent gaps"
            ),
            "finite_width_warning": (
                "remaining merge capacity is computed from each declared suffix language, "
                "not by a width-independent local formula"
            ),
        },
        "training_certificate": {
            **{key: value for key, value in training.items() if key != "potentials"},
            "complete_source_census": {
                source["name"]: {
                    "feature_states": len(source["features"]),
                    "transitions": len(source["transitions"]),
                    "terminal_features": len(source["terminals"]),
                }
                for source in complete
            },
            "terminal_constant": 5,
            "potential_table": training["potentials"],
        },
        "feature_ablation": _ablation_collisions(complete),
        "heldout_fixed_paths": heldout,
        "fixed_path_extension_certificate": {
            **{key: value for key, value in fixed_extension.items() if key != "potentials"},
            "interpretation": (
                "The fixed paths extend the exact system consistently. They are not "
                "covered by the n=5,8 table because most projected states are new."
            ),
        },
        "n17_baseline_extension": {
            "path_total_weight": n17["total_weight"],
            "baseline_terminal_constant": 5,
            "total_available_slack": n17["total_weight"] - 5,
            **{key: value for key, value in n17_extension.items() if key != "potentials"},
        },
        "n17_terminal_debt": _terminal_debt_control(),
        "result": {
            "terminal_constant_five": (
                "supported exactly on all complete n=5,8 equality transitions and "
                "consistent with fixed n=11,n=14 and affine n=17 path extensions"
            ),
            "n17_extra_unit": (
                "not supported by this conservative feature potential: the accepted "
                "n17 terminal feature already has potential -5, so forcing -8 conflicts "
                "with the training anchor. Unpayable debt separates the failed u178 "
                "terminal states only in the final-two-cell artifact."
            ),
        },
        "next_obligation": (
            "Replace suffix-enumerated merge capacity by a covered local upper bound and "
            "carry a persistent unpayable-debt or spent-merge flag to the terminal; then "
            "recheck all low-curvature symbolic transitions."
        ),
        "limitations": [
            "This is an exact projected certificate only for enumerated transitions.",
            "The n=11,n=14 extensions are one fixed path each, not complete corridors.",
            "Feasible extension to the 179-U n17 path does not cover any 178-U prefix history.",
            "The committed n17 survivor dump has no backpointers, so terminal unpayable debt cannot be telescoped to the top cap.",
        ],
        "provenance": {
            "producer": "analysis/residue_two_cap_merge_potential.py",
            "command": [
                "python3",
                "-B",
                "analysis/residue_two_cap_merge_potential.py",
                "--output",
                "analysis/residue_two_cap_merge_potential.json",
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
        print(f"cap/merge potential certificate matches {args.output}")
    else:
        args.output.write_text(rendered)
        print(f"wrote {args.output}")


if __name__ == "__main__":
    main()
