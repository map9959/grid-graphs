#!/usr/bin/env python3
"""Test simple max-over-interval potentials on exact forced-forest transitions."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from analysis.bounds.coupled_interval_potential import Source, enumerate_source


def interval_scores(width, state):
    if state is None:
        return []
    scores = []
    for left in range(width):
        forced = 0
        h_labels = set()
        f_labels = set()
        for right in range(left + 1, width + 1):
            forced += bool(state.forced_mask & (1 << (right - 1)))
            h_labels.add(state.h_partition[right - 1])
            if state.f_partition[right - 1] >= 0:
                f_labels.add(state.f_partition[right - 1])
            scores.append((
                right - left,
                forced,
                len(h_labels),
                len(f_labels),
                int(bool(state.forced_mask & (1 << left))),
                int(bool(state.forced_mask & (1 << (right - 1)))),
            ))
    return scores


def potential(width, row, state, coefficients):
    if state is None:
        return 0
    (a_len, a_forced, a_h, a_f, a_left, a_right, constant, terminal,
     a_retired_h, a_retired_f) = coefficients
    return (terminal if row == width else 0) + a_retired_h * state.retired_h \
        + a_retired_f * state.retired_f + max(
        constant + a_len * length + a_forced * forced + a_h * h_rank
        + a_f * f_rank + a_left * left + a_right * right
        for length, forced, h_rank, f_rank, left, right in interval_scores(width, state)
    )


def packed_potential(width, row, state, coefficients, vectors=None):
    """Maximum total score of pairwise disjoint nonempty frontier intervals."""
    if state is None:
        return 0
    (a_len, a_forced, a_h, a_f, a_left, a_right, constant, terminal,
     a_retired_h, a_retired_f) = coefficients
    scores = interval_scores(width, state) if vectors is None else vectors
    by_right = [[] for _ in range(width + 1)]
    index = 0
    for left in range(width):
        for right in range(left + 1, width + 1):
            length, forced, h_rank, f_rank, left_bit, right_bit = scores[index]
            index += 1
            score = constant + a_len * length + a_forced * forced + a_h * h_rank \
                + a_f * f_rank + a_left * left_bit + a_right * right_bit
            by_right[right].append((left, score))
    best = [0] * (width + 1)
    for right in range(1, width + 1):
        best[right] = best[right - 1]
        for left, score in by_right[right]:
            best[right] = max(best[right], best[left] + score)
    return (terminal if row == width else 0) + a_retired_h * state.retired_h \
        + a_retired_f * state.retired_f + best[width]


def check(sources: list[Source], coefficients):
    worst = None
    for source in sources:
        for state in source.layers[-1]:
            if state is None:
                continue
            slack = potential(source.width, source.width, state, coefficients) - 4
            if worst is None or slack < worst[0]:
                worst = (slack, "terminal", source.width, state)
        for row_edges in source.edges:
            for edge in row_edges:
                slack = edge.weight - (
                    potential(edge.width, edge.row + 1, edge.outgoing, coefficients)
                    - potential(edge.width, edge.row, edge.incoming, coefficients)
                )
                if worst is None or slack < worst[0]:
                    worst = (slack, "edge", edge)
    return worst


def search(widths, bound):
    sources = [enumerate_source(width) for width in widths]
    vectors = {}
    for source in sources:
        for row, layer in enumerate(source.layers):
            for state in layer:
                if state is not None:
                    vectors[(source.width, row, state)] = interval_scores(source.width, state)
    terminals = [
        (source.width, state)
        for source in sources
        for state in source.layers[-1]
        if state is not None
    ]
    edges = [edge for source in sources for row_edges in source.edges for edge in row_edges]

    def fast_potential(width, row, state, coefficients):
        if state is None:
            return 0
        return packed_potential(
            width, row, state, coefficients, vectors[(width, row, state)]
        )

    def fast_check(coefficients):
        worst = None
        for width, state in terminals:
            slack = fast_potential(width, width, state, coefficients) - 4
            if worst is None or slack < worst[0]:
                worst = (slack, "terminal", width, state)
            if slack < 0:
                return worst
        for edge in edges:
            slack = edge.weight - (
                fast_potential(edge.width, edge.row + 1, edge.outgoing, coefficients)
                - fast_potential(edge.width, edge.row, edge.incoming, coefficients)
            )
            if worst is None or slack < worst[0]:
                worst = (slack, "edge", edge)
            if slack < 0:
                return worst
        return worst

    best = None
    for a_len in range(-bound, bound + 1):
        for a_forced in range(-bound, bound + 1):
            for a_h in range(-bound, bound + 1):
                for a_f in range(-bound, bound + 1):
                    for a_left in range(-bound, bound + 1):
                        for a_right in range(-bound, bound + 1):
                            for constant in range(-bound, bound + 1):
                                for terminal in range(0, 5):
                                    coefficients = (
                                        a_len, a_forced, a_h, a_f, a_left,
                                        a_right, constant, terminal, 1, 1,
                                    )
                                    worst = fast_check(coefficients)
                                    if best is None or worst[0] > best[0]:
                                        best = worst[0], coefficients, worst
                                    if worst[0] >= 0:
                                        return {
                                            "found": True,
                                            "coefficients": coefficients,
                                            "minimum_slack": worst[0],
                                        }
    return {"found": False, "best": best}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--widths", type=int, nargs="+", default=[3, 4, 5])
    parser.add_argument("--bound", type=int, default=2)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = search(args.widths, args.bound)
    rendered = json.dumps(result, default=repr, indent=2) + "\n"
    if args.output:
        args.output.write_text(rendered)
    else:
        print(rendered, end="")
