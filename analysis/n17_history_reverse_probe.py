#!/usr/bin/env python3
"""Bounded exact reverse-transition probe for the committed n=17 dump.

This enumerates transition-valid predecessors, not forward-reachable ones.  The
distinction is the point of the probe: the dump contains no reachability index
for earlier layers.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter
from dataclasses import dataclass
from functools import cache
from pathlib import Path

import residue_two_attachment_history as attachment
from residue_two_attachment_history import Frontier


HERE = Path(__file__).resolve().parent
DUMP = HERE / "frontier_n17_u178_step287.json"


# The reference analyzer rebuilds the schedule on each call because its normal
# workload is two cells.  Reverse probing calls it many times, so memoize only
# these pure schedule functions without changing their transition semantics.
attachment._bags = cache(attachment._bags)
attachment._edges = cache(attachment._edges)


@dataclass(frozen=True, slots=True)
class State:
    completed: int
    labels: tuple[int, ...]
    row_u: int
    cost: int

    @property
    def debt(self) -> int:
        return len(set(self.labels) - {self.labels[0]})


def terminal_edge_capacity(n: int, state: State, target: int) -> int:
    """Exact maximum active edges in the unprocessed final-row suffix."""
    row, first_col = divmod(state.completed, n)
    if row != n - 1:
        raise ValueError("probe capacity is defined only in the final row")
    budget = target - state.cost
    left_u = int(first_col > 0 and bool(state.row_u & (1 << (first_col - 1))))
    dynamic = {(0, left_u): 0}
    for col in range(first_col, n):
        following = {}
        upper_u = int(bool(state.row_u & (1 << col)))
        for (used, previous_u), edges in dynamic.items():
            following[(used, 0)] = max(following.get((used, 0), -1), edges)
            if used < budget:
                value = edges + previous_u + upper_u
                following[(used + 1, 1)] = max(
                    following.get((used + 1, 1), -1), value
                )
        dynamic = following
    return min(state.debt, max(dynamic.values(), default=0))


def _canonical(labels: tuple[int, ...]) -> bool:
    return bool(labels) and labels[0] == 0 and all(
        value <= max(labels[:index], default=-1) + 1
        for index, value in enumerate(labels)
    )


def _partitions(length: int, maximum_components: int):
    labels = [0] * length

    def visit(slot: int, used: int):
        if slot == length:
            yield tuple(labels)
            return
        for label in range(min(used, maximum_components - 1) + 1):
            labels[slot] = label
            yield from visit(slot + 1, max(used, label + 1))

    if length and maximum_components:
        yield from visit(1, 1)


def reverse_predecessors(n: int, post: State) -> list[State]:
    """Exact but deliberately simple inverse of one Rust advance transition."""
    at = post.completed - 1
    row, col = divmod(at, n)
    before, work, after = attachment._bags(n, at)
    if len(after) != len(post.labels):
        raise ValueError("post-state bag does not match schedule")
    chosen = bool(post.row_u & (1 << col))
    introduced = len(work) - len(before)
    # At most two active edges are added, so inversion can split at most twice.
    maximum_components = len(set(post.labels)) + 2 - introduced
    result = []
    for previous_up in (False, True):
        row_u = post.row_u | (1 << col) if previous_up else post.row_u & ~(1 << col)
        predecessor_cost = post.cost - int(chosen)
        for labels in _partitions(len(before), maximum_components):
            if not _canonical(labels):
                continue
            candidate = Frontier(at, labels, row_u, predecessor_cost)
            following, _ = attachment.advance_cell(n, candidate, chosen)
            if following is None:
                continue
            if (
                following.labels == post.labels
                and following.row_u == post.row_u
                and following.cost == post.cost
            ):
                result.append(State(at, labels, row_u, predecessor_cost))
    return sorted(set(result), key=lambda state: (state.labels, state.row_u, state.cost))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--depth", type=int, default=2, choices=range(1, 5))
    args = parser.parse_args()
    source = json.loads(DUMP.read_text())
    layer = {
        State(source["completed_steps"], tuple(item["labels"]), item["row_u"], item["cost"])
        for item in source["states"]
    }
    ordered_roots = sorted(layer, key=lambda state: (state.labels, state.row_u, state.cost))
    origins = {state: 1 << index for index, state in enumerate(ordered_roots)}
    report = {
        "dump_states": len(layer),
        "start_step": source["completed_steps"],
        "warning": "all predecessors are transition-valid; forward reachability is unknown",
        "layers": [],
    }
    for _ in range(args.depth):
        multiplicities = Counter()
        previous = set()
        previous_origins = {}
        for post in layer:
            predecessors = reverse_predecessors(source["n"], post)
            multiplicities[len(predecessors)] += 1
            for predecessor in predecessors:
                previous.add(predecessor)
                previous_origins[predecessor] = (
                    previous_origins.get(predecessor, 0) | origins[post]
                )
        deficits = {
            state: state.debt
            - terminal_edge_capacity(source["n"], state, source["target"])
            for state in previous
        }
        minimum_by_root = []
        maximum_by_root = []
        for root in range(len(ordered_roots)):
            root_deficits = [
                deficit
                for state, deficit in deficits.items()
                if previous_origins[state] & (1 << root)
            ]
            minimum_by_root.append(min(root_deficits))
            maximum_by_root.append(max(root_deficits))
        report["layers"].append(
            {
                "from_step": next(iter(layer)).completed,
                "post_states": len(layer),
                "predecessor_multiplicity": dict(sorted(multiplicities.items())),
                "distinct_candidate_predecessors": len(previous),
                "candidate_debt_histogram": dict(
                    sorted(Counter(state.debt for state in previous).items())
                ),
                "candidate_cost_histogram": dict(
                    sorted(Counter(state.cost for state in previous).items())
                ),
                "unpayable_debt_histogram": dict(
                    sorted(Counter(deficits.values()).items())
                ),
                "survivor_minimum_unpayable_debt_histogram": dict(
                    sorted(Counter(minimum_by_root).items())
                ),
                "survivor_maximum_unpayable_debt_histogram": dict(
                    sorted(Counter(maximum_by_root).items())
                ),
                "survivor_row_u_with_zero_candidate": [
                    ordered_roots[index].row_u
                    for index, value in enumerate(minimum_by_root)
                    if value == 0
                ],
                "survivors_forced_positive_at_cut": sum(
                    value > 0 for value in minimum_by_root
                ),
            }
        )
        layer = previous
        origins = previous_origins
        if not layer:
            break
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
