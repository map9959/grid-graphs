#!/usr/bin/env python3
"""Exact per-owner minimum-reflex gate for maximal forced forests.

For every omitted owner, all insertion circuits are obtained from paths in the
forced forest H.  Circuit choices have no shared constraint, so minimizing the
total number of reflex corners is exactly the sum of the owner-wise minima.
The small-width census is exhaustive; larger-width results are adversarial
finite searches whose candidates are certified by the exact row grammar.
"""

from __future__ import annotations

import argparse
import json
import random
import time
from collections import Counter, deque
from dataclasses import asdict, dataclass
from itertools import combinations
from typing import Iterable

from analysis.bounds.boundary_charge_reduction import canonical_rows
from analysis.bounds.bundle_cycle_defect_census import (
    DefectProfile,
    TARGETED_MAXIMUM_WITNESSES,
    defect_profile,
    maximal_profiles,
    maximalize,
    neighbors,
    render_rows,
)


KNOWN_COUNTEREXAMPLE = (255, 0, 292, 293, 289, 297, 257, 256, 383)


@dataclass(frozen=True)
class MinimumReflexProfile:
    n: int
    forced: int
    unforced: int
    unforced_components: int
    minimum_reflex: int
    positive_reflex_owners: int
    maximum_owner_minimum: int
    owner_minimum_distribution: tuple[tuple[int, int], ...]
    target_slack_before_reflex: int
    objective: int

    @property
    def equality(self) -> bool:
        return self.objective == 0

    @property
    def counterexample(self) -> bool:
        return self.objective > 0


class _ForestPaths:
    """Rooted-forest index supporting exact paths in time proportional to length."""

    def __init__(self, adjacency: tuple[tuple[int, ...], ...]) -> None:
        size = len(adjacency)
        self.parent = [-1] * size
        self.depth = [0] * size
        self.root = [-1] * size
        for start in range(size):
            if self.root[start] >= 0:
                continue
            self.root[start] = start
            queue = deque([start])
            while queue:
                vertex = queue.popleft()
                for other in adjacency[vertex]:
                    if other == self.parent[vertex]:
                        continue
                    if self.root[other] >= 0:
                        raise AssertionError("H must be a forest")
                    self.root[other] = start
                    self.parent[other] = vertex
                    self.depth[other] = self.depth[vertex] + 1
                    queue.append(other)

    def path(self, start: int, finish: int) -> tuple[int, ...] | None:
        if self.root[start] != self.root[finish]:
            return None
        left = []
        right = []
        a, b = start, finish
        while self.depth[a] > self.depth[b]:
            left.append(a)
            a = self.parent[a]
        while self.depth[b] > self.depth[a]:
            right.append(b)
            b = self.parent[b]
        while a != b:
            left.append(a)
            right.append(b)
            a = self.parent[a]
            b = self.parent[b]
        return tuple(left + [a] + list(reversed(right)))


def _turns(n: int, cycle: tuple[int, ...]) -> int:
    points = [divmod(vertex, n) for vertex in cycle[:-1]]
    turns = 0
    for index, current in enumerate(points):
        previous = points[index - 1]
        following = points[(index + 1) % len(points)]
        incoming = (current[0] - previous[0], current[1] - previous[1])
        outgoing = (following[0] - current[0], following[1] - current[1])
        turns += incoming != outgoing
    return turns


def _reflex_corners(n: int, cycle: tuple[int, ...]) -> int:
    turns = _turns(n, cycle)
    if turns < 4 or (turns - 4) % 2:
        raise AssertionError("simple rectilinear cycle has turns = 4 + 2R")
    return (turns - 4) // 2


def _owner_minimum_reflex_counts(n: int, rows: tuple[int, ...]) -> tuple[int, ...]:
    forced = {
        row * n + column
        for row, mask in enumerate(rows)
        for column in range(n)
        if mask >> column & 1
    }
    unforced = set(range(n * n)) - forced
    adjacency = tuple(
        tuple(other for other in neighbors(n, vertex) if vertex in forced or other in forced)
        for vertex in range(n * n)
    )
    paths = _ForestPaths(adjacency)
    minima = []
    for owner in sorted(unforced):
        leaves = tuple(other for other in neighbors(n, owner) if other in unforced)
        candidates = []
        for leaf in leaves:
            path = paths.path(leaf, owner)
            if path is not None:
                candidates.append(_reflex_corners(n, (owner,) + path))
        for left, right in combinations(leaves, 2):
            path = paths.path(left, right)
            if path is not None and owner not in path:
                candidates.append(_reflex_corners(n, (owner,) + path + (owner,)))
        if not candidates:
            raise AssertionError("maximality did not produce an insertion circuit")
        minima.append(min(candidates))
    return tuple(minima)


def owner_minimum_reflex_counts(n: int, rows: Iterable[int]) -> tuple[int, ...]:
    """Return the exact minimum reflex count independently for every owner."""
    rows = tuple(rows)
    if not defect_profile(n, rows).maximal:
        raise ValueError("rows must encode an inclusion-maximal forced forest")
    return _owner_minimum_reflex_counts(n, rows)


def _minimum_reflex_profile(
    n: int, rows: tuple[int, ...], base: DefectProfile
) -> MinimumReflexProfile:
    if not base.maximal:
        raise ValueError("rows must encode an inclusion-maximal forced forest")
    minima = _owner_minimum_reflex_counts(n, rows)
    minimum_reflex = sum(minima)
    target_slack = (
        n * n + 3 * n - 3 * base.forced - base.unforced_induced_components - 3
    )
    return MinimumReflexProfile(
        n=n,
        forced=base.forced,
        unforced=base.unforced,
        unforced_components=base.unforced_induced_components,
        minimum_reflex=minimum_reflex,
        positive_reflex_owners=sum(value > 0 for value in minima),
        maximum_owner_minimum=max(minima, default=0),
        owner_minimum_distribution=tuple(sorted(Counter(minima).items())),
        target_slack_before_reflex=target_slack,
        objective=2 * minimum_reflex - target_slack,
    )


def minimum_reflex_profile(n: int, rows: Iterable[int]) -> MinimumReflexProfile:
    rows = tuple(rows)
    base = defect_profile(n, rows)
    return _minimum_reflex_profile(n, rows, base)


def _witness(rows: tuple[int, ...], profile: MinimumReflexProfile) -> dict:
    return {"rows": render_rows(rows), "profile": asdict(profile)}


def summarize(n: int, coverage: str, samples: list[tuple[tuple[int, ...], MinimumReflexProfile]]) -> dict:
    if not samples:
        return {"n": n, "coverage": coverage, "checked": 0}
    best_value = max(profile.objective for _rows, profile in samples)
    positive = [(rows, profile) for rows, profile in samples if profile.minimum_reflex > 0]
    best_positive = max((profile.objective for _rows, profile in positive), default=None)
    return {
        "n": n,
        "coverage": coverage,
        "checked": len(samples),
        "maximum_objective": best_value,
        "counterexamples": sum(profile.counterexample for _rows, profile in samples),
        "equalities": sum(profile.equality for _rows, profile in samples),
        "positive_reflex_checked": len(positive),
        "positive_reflex_equalities": sum(profile.equality for _rows, profile in positive),
        "maximum_positive_reflex_objective": best_positive,
        "equality_structure_distribution": {
            str(key): count
            for key, count in sorted(
                Counter(
                    (
                        profile.forced,
                        profile.unforced_components,
                        profile.minimum_reflex,
                        profile.positive_reflex_owners,
                        profile.maximum_owner_minimum,
                    )
                    for _rows, profile in samples
                    if profile.equality
                ).items()
            )
        },
        "first_maximum_witness": next(
            _witness(rows, profile)
            for rows, profile in samples
            if profile.objective == best_value
        ),
        "first_maximum_positive_reflex_witness": next(
            (
                _witness(rows, profile)
                for rows, profile in positive
                if profile.objective == best_positive
            ),
            None,
        ),
    }


def adversarial_reflex_witnesses(
    n: int, attempts: int, seed: int
) -> list[tuple[tuple[int, ...], MinimumReflexProfile]]:
    """Maximize REFL, maintaining a separate hill climb constrained to R>0."""
    rng = random.Random(seed)
    vertices = list(range(n * n))
    retained: dict[tuple[int, ...], MinimumReflexProfile] = {}

    def evaluate(rows: tuple[int, ...]) -> tuple[tuple[int, ...], MinimumReflexProfile]:
        base = defect_profile(n, rows)
        if not base.maximal:
            order = vertices.copy()
            rng.shuffle(order)
            rows = maximalize(n, rows, order)
            base = defect_profile(n, rows)
        if rows not in retained:
            retained[rows] = _minimum_reflex_profile(n, rows, base)
        return rows, retained[rows]

    initial = {*TARGETED_MAXIMUM_WITNESSES.get(n, ())}
    try:
        initial.add(canonical_rows(n))
    except (KeyError, ValueError):
        # The explicit pattern library intentionally starts above tiny widths.
        initial.add((0,) * n)
    if n == 9:
        initial.add(KNOWN_COUNTEREXAMPLE)
    evaluated = [evaluate(rows) for rows in initial]
    best = max(evaluated, key=lambda item: item[1].objective)
    positive = [item for item in evaluated if item[1].minimum_reflex > 0]
    best_positive = max(positive, key=lambda item: item[1].objective, default=None)
    current = best

    for attempt in range(attempts):
        if attempt % max(1, attempts // 8) == 0:
            order = vertices.copy()
            rng.shuffle(order)
            candidate = maximalize(n, (0,) * n, order)
        else:
            anchors = [current, best]
            if best_positive is not None:
                anchors.append(best_positive)
            anchor_rows, _anchor_profile = rng.choice(anchors)
            forced = [
                vertex
                for vertex in vertices
                if anchor_rows[vertex // n] >> (vertex % n) & 1
            ]
            proposal = list(anchor_rows)
            for vertex in rng.sample(forced, min(len(forced), rng.choice((1, 1, 2, 3, 4)))):
                proposal[vertex // n] &= ~(1 << (vertex % n))
            order = vertices.copy()
            rng.shuffle(order)
            candidate = maximalize(n, tuple(proposal), order)
        item = evaluate(candidate)
        if item[1].objective > best[1].objective:
            best = item
        if item[1].minimum_reflex > 0 and (
            best_positive is None or item[1].objective > best_positive[1].objective
        ):
            best_positive = item
        if item[1].objective >= current[1].objective or rng.random() < 0.06:
            current = item
    return sorted(retained.items())


def build_report(exhaustive_through: int = 5, adversarial_through: int = 21, attempts: int = 128) -> dict:
    started = time.perf_counter()
    records = []
    counterexample = None
    for n in range(2, exhaustive_through + 1):
        samples = [
            (rows, minimum_reflex_profile(n, rows))
            for rows, _base in maximal_profiles(n)
        ]
        records.append(summarize(n, "all inclusion-maximal sets", samples))
        if counterexample is None:
            counterexample = next(
                (_witness(rows, profile) for rows, profile in samples if profile.counterexample),
                None,
            )
    for n in range(max(2, exhaustive_through + 1), adversarial_through + 1):
        samples = adversarial_reflex_witnesses(n, attempts, 49979687 + 1009 * n)
        records.append(summarize(n, "row-grammar adversarial maximal sets", samples))
        if counterexample is None:
            counterexample = next(
                (_witness(rows, profile) for rows, profile in samples if profile.counterexample),
                None,
            )
    return {
        "scope": "finite computation only; exhaustive only where explicitly stated",
        "objective": "2*R_min+3*|F|+c(G[U])+3-(n^2+3n)",
        "optimization": "R_min is the sum of independent per-owner circuit minima",
        "counterexample": counterexample,
        "records": records,
        "seconds": round(time.perf_counter() - started, 3),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exhaustive-through", type=int, default=5)
    parser.add_argument("--adversarial-through", type=int, default=21)
    parser.add_argument("--attempts", type=int, default=128)
    parser.add_argument("--output")
    args = parser.parse_args()
    report = build_report(args.exhaustive_through, args.adversarial_through, args.attempts)
    encoded = json.dumps(report, indent=2)
    print(encoded)
    if args.output:
        with open(args.output, "w", encoding="ascii") as destination:
            destination.write(encoded + "\n")
    if report["counterexample"] is not None:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
