#!/usr/bin/env python3
"""Exact product monitor for the forced-forest favorable-side conjecture.

For every F whose forced graph H is a forest, test whether some boundary side S
satisfies

    |F intersect S| <= c(G[F]) + c(H) - 2.

The four corners belong to both incident sides.  This is a finite exhaustive
computation only; success at the requested widths is not an asymptotic claim.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

from forced_forest_row_grammar import (
    State,
    _DisjointSet,
    first_row_state,
    is_forced_forest,
    transition,
)


FPartition = tuple[int, ...]  # -1 marks a vertex outside F.


@dataclass(frozen=True)
class MonitorState:
    h_state: State
    f_partition: FPartition
    retired_h: int
    retired_f: int
    top: int
    left: int
    right: int


@dataclass(frozen=True)
class Counterexample:
    n: int
    row_masks: tuple[int, ...]
    side_counts: tuple[int, int, int, int]
    c_f: int
    c_h: int


def _canonical_f_partition(
    dsu: _DisjointSet, vertices: Iterable[int], forced_mask: int, offset: int
) -> FPartition:
    labels: dict[int, int] = {}
    result = []
    for column, vertex in enumerate(vertices):
        if not forced_mask & (1 << column):
            result.append(-1)
            continue
        root = dsu.find(vertex)
        if root not in labels:
            labels[root] = len(labels)
        result.append(labels[root])
    return tuple(result)


def first_monitor_state(width: int, mask: int) -> MonitorState | None:
    h_state = first_row_state(width, mask)
    if h_state is None:
        return None
    dsu = _DisjointSet(width)
    for column in range(width - 1):
        if mask & (1 << column) and mask & (1 << (column + 1)):
            if not dsu.union_edge(column, column + 1):
                raise AssertionError("a row path cannot cycle")
    f_partition = _canonical_f_partition(dsu, range(width), mask, 0)
    return MonitorState(
        h_state=h_state,
        f_partition=f_partition,
        retired_h=0,
        retired_f=0,
        top=mask.bit_count(),
        left=mask & 1 != 0,
        right=mask & (1 << (width - 1)) != 0,
    )


def monitor_transition(width: int, state: MonitorState, mask: int) -> MonitorState | None:
    next_h = transition(width, state.h_state, mask)
    if next_h is None:
        return None

    h_contacts = {
        state.h_state.partition[column]
        for column in range(width)
        if (state.h_state.forced_mask | mask) & (1 << column)
    }
    retired_h = state.retired_h + len(set(state.h_state.partition) - h_contacts)

    dsu = _DisjointSet(2 * width)
    representatives: dict[int, int] = {}
    for column, label in enumerate(state.f_partition):
        if label < 0:
            continue
        if label in representatives:
            dsu.union_summary(representatives[label], column)
        else:
            representatives[label] = column

    old_mask = state.h_state.forced_mask
    f_contacts = set()
    for column in range(width):
        if old_mask & mask & (1 << column):
            label = state.f_partition[column]
            f_contacts.add(label)
            if not dsu.union_edge(column, width + column):
                raise AssertionError("G[F] cycled inside a forest H")
    for column in range(width - 1):
        if mask & (1 << column) and mask & (1 << (column + 1)):
            if not dsu.union_edge(width + column, width + column + 1):
                raise AssertionError("G[F] cycled inside a forest H")
    active_f = {label for label in state.f_partition if label >= 0}
    retired_f = state.retired_f + len(active_f - f_contacts)
    next_f = _canonical_f_partition(
        dsu, range(width, 2 * width), mask, width
    )
    return MonitorState(
        h_state=next_h,
        f_partition=next_f,
        retired_h=retired_h,
        retired_f=retired_f,
        top=state.top,
        left=state.left + bool(mask & 1),
        right=state.right + bool(mask & (1 << (width - 1))),
    )


def terminal_counts(width: int, state: MonitorState) -> tuple[tuple[int, ...], int, int]:
    c_h = state.retired_h + len(set(state.h_state.partition))
    c_f = state.retired_f + len({label for label in state.f_partition if label >= 0})
    sides = (state.top, state.right, state.h_state.forced_mask.bit_count(), state.left)
    return sides, c_f, c_h


def find_counterexample(n: int) -> tuple[Counterexample | None, dict[str, int]]:
    """Exhaust the product grammar and return one counterexample if present."""
    if n <= 0:
        raise ValueError("n must be positive")
    states: dict[MonitorState, tuple[int, ...]] = {}
    for mask in range(1 << n):
        state = first_monitor_state(n, mask)
        if state is not None:
            states.setdefault(state, (mask,))
    peak = len(states)
    transitions_tested = 1 << n
    for _row in range(1, n):
        next_states: dict[MonitorState, tuple[int, ...]] = {}
        for state, rows in states.items():
            for mask in range(1 << n):
                transitions_tested += 1
                outgoing = monitor_transition(n, state, mask)
                if outgoing is not None:
                    next_states.setdefault(outgoing, rows + (mask,))
        states = next_states
        peak = max(peak, len(states))

    for state, rows in states.items():
        sides, c_f, c_h = terminal_counts(n, state)
        if min(sides) > c_f + c_h - 2:
            return Counterexample(n, rows, sides, c_f, c_h), {
                "terminal_states": len(states),
                "peak_states": peak,
                "transitions_tested": transitions_tested,
            }
    return None, {
        "terminal_states": len(states),
        "peak_states": peak,
        "transitions_tested": transitions_tested,
    }


def direct_counts(n: int, rows: tuple[int, ...]) -> tuple[tuple[int, ...], int, int]:
    """Independently count sides and components from the full vertex set."""
    if len(rows) != n:
        raise ValueError("row count does not match n")
    h = _DisjointSet(n * n)
    f = _DisjointSet(n * n)
    f_vertices = []
    h_edges = 0
    f_edges = 0
    for row in range(n):
        for column in range(n):
            vertex = row * n + column
            forced = bool(rows[row] & (1 << column))
            if forced:
                f_vertices.append(vertex)
            for dr, dc in ((0, 1), (1, 0)):
                other_row, other_column = row + dr, column + dc
                if other_row >= n or other_column >= n:
                    continue
                other = other_row * n + other_column
                other_forced = bool(rows[other_row] & (1 << other_column))
                if forced or other_forced:
                    if not h.union_edge(vertex, other):
                        raise ValueError("H is cyclic")
                    h_edges += 1
                if forced and other_forced:
                    if not f.union_edge(vertex, other):
                        raise ValueError("G[F] is cyclic")
                    f_edges += 1
    sides = (
        rows[0].bit_count(),
        sum(bool(mask & (1 << (n - 1))) for mask in rows),
        rows[-1].bit_count(),
        sum(bool(mask & 1) for mask in rows),
    )
    # These edge-count identities are independent of frontier retirement.
    return sides, len(f_vertices) - f_edges, n * n - h_edges


def verify_counterexample(counterexample: Counterexample) -> None:
    if not is_forced_forest(counterexample.n, list(counterexample.row_masks)):
        raise AssertionError("reported H is not a forest")
    observed = direct_counts(counterexample.n, counterexample.row_masks)
    expected = (counterexample.side_counts, counterexample.c_f, counterexample.c_h)
    if observed != expected:
        raise AssertionError(f"independent counts disagree: {observed} != {expected}")
    if min(counterexample.side_counts) <= counterexample.c_f + counterexample.c_h - 2:
        raise AssertionError("reported candidate is not a counterexample")


def run_scope(max_n: int) -> dict:
    results = []
    counterexample = None
    for n in range(1, max_n + 1):
        found, census = find_counterexample(n)
        result = {"n": n, "counterexample": found is not None, **census}
        results.append(result)
        if found is not None:
            verify_counterexample(found)
            counterexample = {
                "n": n,
                "rows": [format(mask, f"0{n}b")[::-1] for mask in found.row_masks],
                "side_order": ["top", "right", "bottom", "left"],
                "side_counts": list(found.side_counts),
                "c_F": found.c_f,
                "c_H": found.c_h,
                "threshold": found.c_f + found.c_h - 2,
                "independent_verification": "full-grid DSU plus |V|-|E| component counts",
            }
            break
    return {
        "claim": "some side S has |F intersect S| <= c_F+c_H-2",
        "method": "complete exact product row grammar with exact component retirement",
        "corners": "counted on both incident sides",
        "results": results,
        "counterexample": counterexample,
        "scope_limit": "finite tested widths only; no width-independent conclusion",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, default=8)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    artifact = run_scope(args.max_n)
    rendered = json.dumps(artifact, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(rendered)
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
