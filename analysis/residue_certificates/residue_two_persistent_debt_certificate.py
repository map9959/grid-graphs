#!/usr/bin/env python3
"""Persistent spent-merge histories with safe local capacity bounds.

The local bound never inspects an accepting suffix.  Complete n=5,8 equality
corridors are lifted to histories carrying U/rank expenditure and spent merges.
The n=17 terminal control uses only its current cut state and remaining budget.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path

from analysis._paths import ANALYSIS_ROOT
from analysis.bounds.proof_oriented_identities import tile_grammar_row_deltas
from analysis.patterns.diagonal_patterns import (
    q_old_formula,
    residue_two_affine_pattern,
    residue_two_explicit_pattern,
)
from analysis.residue_certificates.residue_two_attachment_history import (
    Frontier,
)
from analysis.residue_certificates.residue_two_attachment_history import (
    build_analysis as build_attachment_history,
)
from analysis.residue_certificates.residue_two_attachment_skeleton import (
    linear_frontier_metric,
)
from analysis.residue_certificates.residue_two_cap_merge_potential import (
    ProjectedTransition,
    _difference_certificate,
    cap_phase,
)
from analysis.residue_certificates.residue_two_local_motif_grammar import (
    maximum_face_cut_open_width,
)
from analysis.residue_certificates.residue_two_n11_grammar_counterexample import (
    ROWS as N11_SILENT_ROWS,
)
from analysis.tiles.tile_grammar import (
    FrontierState,
    advance_row,
    initial_state,
    row_mask,
)
from analysis.transport.equality_corridor import (
    EqualityCorridor,
    build_equality_corridor,
)

HERE = ANALYSIS_ROOT
DEFAULT_OUTPUT = HERE / "residue_two_persistent_debt_certificate.json"
SCHEMA = "grid-graphs.residue-two-persistent-debt.v1"


@dataclass(frozen=True, slots=True)
class MergeHistory:
    u_spent: int
    rank_spent: int
    spent_merges: int
    created_debt: int
    maximum_unpayable_debt: int


def maximum_terminal_row_edges(n: int, previous_mask: int, u_budget: int) -> int:
    """Exactly maximize active edges while choosing the final row."""
    budget = max(0, min(u_budget, n))
    dp = {(0, 0): 0}
    for column in range(n):
        following = {}
        for (used, left_u), edges in dp.items():
            following[(used, 0)] = max(following.get((used, 0), -1), edges)
            if used < budget:
                value = edges + left_u + int(bool(previous_mask & (1 << column)))
                following[(used + 1, 1)] = max(
                    following.get((used + 1, 1), -1), value
                )
        dp = following
    return max(dp.values(), default=0)


def terminal_cell_edge_capacity(n: int, state: Frontier, u_budget: int) -> int:
    """Exactly maximize active edges in the unprocessed suffix of the last row."""
    row, first_column = divmod(state.completed_steps, n)
    if row != n - 1:
        raise ValueError("exact cell-cap bound requires the final row")
    budget = max(0, u_budget)
    left_u = int(first_column > 0 and bool(state.row_u & (1 << (first_column - 1))))
    dp = {(0, left_u): 0}
    for column in range(first_column, n):
        following = {}
        upper_u = int(bool(state.row_u & (1 << column)))
        for (used, previous_u), edges in dp.items():
            following[(used, 0)] = max(following.get((used, 0), -1), edges)
            if used < budget:
                value = edges + previous_u + upper_u
                following[(used + 1, 1)] = max(
                    following.get((used + 1, 1), -1), value
                )
        dp = following
    return max(dp.values(), default=0)


def local_merge_upper_bound(
    n: int,
    state: FrontierState,
    history: MergeHistory,
    target_u: int,
) -> dict:
    """Return a safe suffix-free upper bound on future independent merges."""
    debt = linear_frontier_metric(state.partition)["attachment_debt"]
    budget = max(target_u - history.u_spent, 0)
    remaining_rank = max((n - 1) ** 2 - history.rank_spent, 0)
    bounds = {
        "current_debt": debt,
        "remaining_rank": remaining_rank,
        "two_edges_per_future_u": 2 * budget,
    }
    if n - state.row_index == 1:
        bounds["exact_terminal_row_edges"] = maximum_terminal_row_edges(
            n, state.previous_u_mask, budget
        )
    return {
        "capacity": min(bounds.values()),
        "debt": debt,
        "remaining_u_budget": budget,
        "bounds": bounds,
    }


def _advance_history(
    n: int,
    incoming_partition: tuple[int, ...],
    outgoing: FrontierState,
    history: MergeHistory,
    d_u: int,
    d_rank: int,
    target_u: int,
) -> MergeHistory:
    debt_in = linear_frontier_metric(incoming_partition)["attachment_debt"]
    debt_out = linear_frontier_metric(outgoing.partition)["attachment_debt"]
    provisional = MergeHistory(
        history.u_spent + d_u,
        history.rank_spent + d_rank,
        history.spent_merges + max(0, debt_in - debt_out),
        history.created_debt + max(0, debt_out - debt_in),
        history.maximum_unpayable_debt,
    )
    local = local_merge_upper_bound(n, outgoing, provisional, target_u)
    return MergeHistory(
        provisional.u_spent,
        provisional.rank_spent,
        provisional.spent_merges,
        provisional.created_debt,
        max(provisional.maximum_unpayable_debt, debt_out - local["capacity"]),
    )


def history_feature(n: int, state: FrontierState, history: MergeHistory, target_u: int) -> tuple:
    metric = linear_frontier_metric(state.partition)
    active_faces = n - 1 if 0 < state.row_index < n else 0
    out = state.partition[0]
    local = local_merge_upper_bound(n, state, history, target_u)
    return (
        cap_phase(n, state.row_index),
        active_faces - metric["attachment_debt"],
        local["capacity"] - metric["attachment_debt"],
        state.previous_u_mask.bit_count(),
        sum(label == out for label in state.partition[1:]),
        metric["branch_cost"],
        maximum_face_cut_open_width(state),
        metric["silent_face_slots"],
        history.spent_merges,
        history.maximum_unpayable_debt,
    )


def lift_corridor(n: int) -> dict:
    corridor = build_equality_corridor(n)
    target_u = q_old_formula(n)
    histories: list[dict[tuple, set[MergeHistory]]] = [defaultdict(set) for _ in range(n + 1)]
    initial_key = next(iter(corridor.corridor_states[0]))
    initial_history = MergeHistory(0, 0, 0, 0, 0)
    histories[0][initial_key].add(initial_history)
    transitions = []
    potential_values: dict[tuple, set[int]] = defaultdict(set)

    for row in range(n):
        for edge in corridor.corridor_edges[row]:
            outgoing = corridor.layers[row + 1][edge.outgoing]
            for history in histories[row].get(edge.incoming, ()):
                following = _advance_history(
                    n,
                    edge.incoming[2],
                    outgoing,
                    history,
                    edge.d_u,
                    edge.d_rank,
                    target_u,
                )
                histories[row + 1][edge.outgoing].add(following)
                incoming_state = corridor.layers[row][edge.incoming]
                incoming_feature = history_feature(n, incoming_state, history, target_u)
                outgoing_feature = history_feature(n, outgoing, following, target_u)
                transitions.append(
                    ProjectedTransition(
                        incoming_feature, outgoing_feature, edge.weight, f"n{n}-complete"
                    )
                )
                potential_values[incoming_feature].add(-corridor.forward[row][edge.incoming])
                potential_values[outgoing_feature].add(
                    -corridor.forward[row + 1][edge.outgoing]
                )

    collisions = {key: values for key, values in potential_values.items() if len(values) > 1}
    if collisions:
        raise AssertionError("persistent history feature has incompatible potentials")
    all_histories = [history for layer in histories for values in layer.values() for history in values]
    if any(history.maximum_unpayable_debt for history in all_histories):
        raise AssertionError("an accepted equality history exceeds a safe local capacity")
    terminals = {
        history_feature(n, corridor.layers[n][key], history, target_u)
        for key, values in histories[n].items()
        for history in values
    }
    return {
        "name": f"n{n}-complete",
        "n": n,
        "corridor": corridor,
        "histories": histories,
        "history_count": len(all_histories),
        "history_features": set(potential_values),
        "potential_values": {key: next(iter(value)) for key, value in potential_values.items()},
        "transitions": transitions,
        "initial": history_feature(n, initial_state(n), initial_history, target_u),
        "terminals": terminals,
        "terminal_histories": sum(len(values) for values in histories[n].values()),
        "spent_merge_range": [
            min(history.spent_merges for history in all_histories),
            max(history.spent_merges for history in all_histories),
        ],
    }


def lift_fixed_path(
    n: int, rows: list[str], name: str, target_u: int | None = None
) -> dict:
    target_u = q_old_formula(n) if target_u is None else target_u
    state = initial_state(n)
    history = MergeHistory(0, 0, 0, 0, 0)
    states = [state]
    histories = [history]
    weights = []
    transitions = []
    for row in rows:
        outgoing = advance_row(state, row_mask(row))
        if outgoing is None:
            raise AssertionError(f"{name} became invalid")
        delta = tile_grammar_row_deltas(state, row_mask(row), outgoing)
        following = _advance_history(
            n,
            state.partition,
            outgoing,
            history,
            delta.u_count,
            delta.rank_delta,
            target_u,
        )
        weight = 3 * delta.u_count - 2 * delta.rank_delta - 1
        transitions.append(
            ProjectedTransition(
                history_feature(n, state, history, target_u),
                history_feature(n, outgoing, following, target_u),
                weight,
                name,
            )
        )
        weights.append(weight)
        states.append(outgoing)
        histories.append(following)
        state, history = outgoing, following
    return {
        "name": name,
        "states": states,
        "histories": histories,
        "features": [
            history_feature(n, state, history, target_u)
            for state, history in zip(states, histories)
        ],
        "transitions": transitions,
        "total_weight": sum(weights),
        "maximum_unpayable_debt": max(item.maximum_unpayable_debt for item in histories),
    }


def n17_terminal_local_control() -> dict:
    analysis = build_attachment_history()
    survivors = analysis["terminal_178"]["states"]
    local_histogram = Counter()
    comparisons = 0
    for item in survivors:
        state = Frontier(
            analysis["terminal_178"]["completed_steps"],
            tuple(item["labels"]) if "labels" in item else (0,),
            item["row_u"],
            item["cost"],
        )
        # build_analysis records no labels in its summarized states; recover them
        # from the rooted debt because every committed survivor has labels 0,1,2.
        state = Frontier(state.completed_steps, (0, 1, 2), state.row_u, state.cost)
        budget = 178 - state.cost
        capacity = min(state.rooted_debt, terminal_cell_edge_capacity(17, state, budget))
        local_histogram[state.rooted_debt - capacity] += 1
        if capacity != item["budgeted_merge_capacity"]:
            raise AssertionError("local terminal edge bound disagrees with suffix capacity")
        comparisons += 1

    replay = json.loads((HERE / "frontier_n17_u179_replay.json").read_text())
    record = next(item for item in replay["records"] if item["completed_steps"] == 287)
    positive = Frontier(287, tuple(record["labels"]), record["row_u"], record["cost"])
    positive_capacity = min(
        positive.rooted_debt,
        terminal_cell_edge_capacity(17, positive, replay["u_count"] - positive.cost),
    )
    return {
        "local_bound": "min(debt, exact active-edge maximum in remaining final-row cells)",
        "u178_states_checked": comparisons,
        "u178_unpayable_debt_histogram": {
            str(value): count for value, count in sorted(local_histogram.items())
        },
        "u179_control": {
            "debt": positive.rooted_debt,
            "local_capacity": positive_capacity,
            "unpayable_debt": positive.rooted_debt - positive_capacity,
        },
        "reconstruction": {
            "u179": "complete explicit pattern replay plus committed step-287 record",
            "u178": (
                "terminal states reconstructed from the committed dump; prefix histories "
                "cannot be reconstructed because the dump has no predecessor IDs"
            ),
        },
    }


def build_artifact() -> dict:
    complete = [lift_corridor(n) for n in (5, 8)]
    transitions = [item for source in complete for item in source["transitions"]]
    anchors = {}
    for source in complete:
        anchors[source["initial"]] = 0
        anchors.update({terminal: -5 for terminal in source["terminals"]})
    certificate = _difference_certificate(transitions, anchors)
    if set(certificate["slack_histogram"]) != {"0"}:
        raise AssertionError("complete equality history edges are not tight")

    fixed = [
        lift_fixed_path(11, residue_two_explicit_pattern(11), "n11-fixed"),
        lift_fixed_path(11, list(N11_SILENT_ROWS), "n11-silent"),
        lift_fixed_path(14, residue_two_explicit_pattern(14), "n14-fixed"),
    ]
    if any(item["maximum_unpayable_debt"] for item in fixed):
        raise AssertionError("a fixed equality path trips the safe local bound")
    extension = _difference_certificate(
        [*transitions, *(edge for source in fixed for edge in source["transitions"])],
        anchors,
    )
    training_features = set().union(*(source["history_features"] for source in complete))

    n17_positive = lift_fixed_path(
        17, residue_two_affine_pattern(17), "n17-affine-179", target_u=179
    )
    n17_extension = _difference_certificate(
        [
            *transitions,
            *(edge for source in fixed for edge in source["transitions"]),
            *n17_positive["transitions"],
        ],
        anchors,
    )
    terminal = n17_terminal_local_control()
    return {
        "schema": SCHEMA,
        "scope": {
            "complete_history_languages": [5, 8],
            "fixed_path_controls": [11, 14, 17],
            "n17_terminal_states": 20,
            "global_low_curvature_coverage_claimed": False,
        },
        "history_channel": {
            "fields": [
                "u_spent",
                "rank_spent",
                "spent_merges",
                "created_debt",
                "maximum_unpayable_debt",
            ],
            "persistence": (
                "maximum_unpayable_debt is monotone and can never be erased by a "
                "later silent-carrier repair"
            ),
            "silent_hull_support": (
                "the state stores face-cut hull width, occurrence branch cost, and "
                "silent hull slots; it does not require contiguous packet support"
            ),
        },
        "local_capacity_theorem": {
            "formula": (
                "capacity <= min(current debt, remaining graphic rank, 2*remaining U; "
                "exact active-edge maximum replaces the last term in the terminal cap)"
            ),
            "safety": [
                "one independent merge reduces at most one live debt component",
                "one independent merge consumes one unit of graphic rank",
                "a future U vertex exposes at most its left and upper processed edges",
                "the final-row dynamic program exhausts all choices under the U budget without using suffix acceptance",
            ],
            "suffix_enumeration_used": False,
        },
        "complete_history_census": {
            source["name"]: {
                "histories": source["history_count"],
                "history_features": len(source["history_features"]),
                "terminal_histories": source["terminal_histories"],
                "spent_merge_range": source["spent_merge_range"],
            }
            for source in complete
        },
        "min_plus_certificate": {
            **{key: value for key, value in certificate.items() if key != "potentials"},
            "terminal_constant": 5,
            "finite_language_theorem": (
                "Every accepting path in the complete augmented n=5,8 equality "
                "languages has charged weight at least five."
            ),
        },
        "fixed_controls": {
            source["name"]: {
                "total_weight": source["total_weight"],
                "maximum_unpayable_debt": source["maximum_unpayable_debt"],
                "states_known_to_training": sum(
                    item in training_features for item in source["features"]
                ),
                "states": len(source["features"]),
            }
            for source in fixed
        },
        "fixed_extension": {
            **{key: value for key, value in extension.items() if key != "potentials"}
        },
        "n17_positive_extension": {
            "path_weight": n17_positive["total_weight"],
            "maximum_unpayable_debt": n17_positive["maximum_unpayable_debt"],
            **{key: value for key, value in n17_extension.items() if key != "potentials"},
        },
        "n17_terminal_separation": terminal,
        "low_curvature_hull_language": {
            "finite_theorem": (
                "Within the explicitly enumerated history languages, silent hull "
                "carriers are allowed, constant five holds, and every represented "
                "n17 u178 terminal state is rejected by positive unpayable debt."
            ),
            "coverage_conjecture": (
                "Every K<=5 path at n=3k+2 is represented by the same bounded hull "
                "state and local-capacity transition language, and for k>=5 its "
                "persistent unpayable-debt channel becomes positive."
            ),
            "coverage_status": "open; no arbitrary-width transition census or proof",
        },
        "result": {
            "baseline_five": "exact finite-language certificate at n=5,8",
            "heldout": "fixed n11,n14 paths extend feasibly but are not covered",
            "n17_extra": (
                "terminal rejection recovered without suffix enumeration, but no u178 "
                "backpointers exist to telescope the persistent channel from the top"
            ),
            "global_k_ge_5": "conjectural pending low-curvature hull-language coverage",
        },
        "next_obligation": (
            "Prove a symbolic transition lemma that updates the local capacity and "
            "persistent deficit for every K<=5 silent-hull packet, or regenerate n17 "
            "u178 survivors with predecessor summaries carrying this history channel."
        ),
        "limitations": [
            "Remaining U budget is a history coordinate tied to the old baseline target.",
            "The generic 2U edge bound is safe but weak away from the terminal cap.",
            "Fixed n11,n14 and n17 controls are single paths or terminal dumps.",
            "No theorem currently forces an arbitrary-width low-curvature path into this finite language.",
        ],
        "provenance": {
            "producer": "analysis/residue_certificates/residue_two_persistent_debt_certificate.py",
            "command": [
                "python3",
                "-B",
                "-m",
                'analysis.residue_certificates.residue_two_persistent_debt_certificate',
                "--output",
                "analysis/residue_two_persistent_debt_certificate.json",
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
        print(f"persistent-debt certificate matches {args.output}")
    else:
        args.output.write_text(rendered)
        print(f"wrote {args.output}")


if __name__ == "__main__":
    main()
