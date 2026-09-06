#!/usr/bin/env python3
"""Aggressive finite falsification of ``3|F| + 2g(F) <= n^2+3n-4``.

The forced graph H(F) contains every grid edge with at least one endpoint in
F.  The domain is exactly the sets for which H(F) is acyclic.

The definition of g used here is deliberately local.  On a binary line, list
its maximal nonempty F-runs in order.  A gap is a pair of consecutive runs,
both of length at least two.  Then g(F) is the sum of this count over all rows
and all columns.  No singleton run is skipped.  Under forced acyclicity this is
the internal axial carrier-gap definition in STRAIGHT_CARRIER_GAP_INEQUALITY.md.

This is finite computational evidence, not a proof for uncomputed sizes.
"""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
import json
import random
import time
from typing import Iterable, Iterator

from analysis.bounds.boundary_charge_reduction import canonical_rows
from analysis.bounds.checkerboard_boundary_runs import acyclic_row_sets
from analysis.bounds.forced_forest_row_grammar import State, first_row_state, is_forced_forest, transition
from analysis.bounds.straight_carrier_inequality import carrier_profile, is_inclusion_maximal


# State after reading a line prefix: neutral, singleton, long run, U-gap after
# a long run, or singleton immediately after such a gap.
NEUTRAL, SINGLETON, LONG_RUN, AFTER_LONG, PENDING_SECOND = range(5)


def line_gap_count(bits: Iterable[bool]) -> int:
    """Count adjacent length-at-least-two F-runs in one finite binary line."""
    state = NEUTRAL
    gaps = 0
    for forced in bits:
        state, gain = _line_step(state, forced)
        gaps += gain
    return gaps


def _line_step(state: int, forced: bool) -> tuple[int, int]:
    if forced:
        if state == NEUTRAL:
            return SINGLETON, 0
        if state == SINGLETON:
            return LONG_RUN, 0
        if state == LONG_RUN:
            return LONG_RUN, 0
        if state == AFTER_LONG:
            return PENDING_SECOND, 0
        if state == PENDING_SECOND:
            return LONG_RUN, 1
    else:
        if state in (NEUTRAL, SINGLETON, PENDING_SECOND):
            return NEUTRAL, 0
        if state in (LONG_RUN, AFTER_LONG):
            return AFTER_LONG, 0
    raise ValueError("invalid line automaton state")


def local_gap_count(n: int, rows: Iterable[int]) -> int:
    """The exact local definition of g(F), symmetric in rows and columns."""
    rows = tuple(rows)
    if n <= 0 or len(rows) != n or any(mask < 0 or mask >= 1 << n for mask in rows):
        raise ValueError("rows must encode an n by n set")
    horizontal = sum(
        line_gap_count(bool(mask & (1 << column)) for column in range(n))
        for mask in rows
    )
    vertical = sum(
        line_gap_count(bool(rows[row] & (1 << column)) for row in range(n))
        for column in range(n)
    )
    return horizontal + vertical


def score(n: int, rows: Iterable[int]) -> int:
    rows = tuple(rows)
    return 3 * sum(mask.bit_count() for mask in rows) + 2 * local_gap_count(n, rows)


def margin(n: int, rows: Iterable[int]) -> int:
    return n * n + 3 * n - 4 - score(n, rows)


def component_gap_count(n: int, rows: Iterable[int]) -> int:
    """Independent global carrier extraction used to validate the local g."""
    return carrier_profile(n, tuple(rows)).internal_u_gaps


def _decode_states(width: int, packed: int) -> list[int]:
    states = []
    for _ in range(width):
        states.append(packed % 5)
        packed //= 5
    return states


def _vertical_step(width: int, packed: int, mask: int) -> tuple[int, int]:
    next_packed = 0
    place = 1
    gain = 0
    for column, state in enumerate(_decode_states(width, packed)):
        next_state, delta = _line_step(state, bool(mask & (1 << column)))
        next_packed += place * next_state
        place *= 5
        gain += delta
    return next_packed, gain


@dataclass(frozen=True)
class ExactMaximum:
    n: int
    maximum: int
    bound: int
    margin: int
    forced_count: int
    gaps: int
    rows: tuple[int, ...]
    layer_states: tuple[int, ...]


def exact_maximum_score(n: int) -> ExactMaximum:
    """Exact weighted row grammar maximizing 3|F|+2g over every acyclic H(F)."""
    if n <= 0:
        raise ValueError("n must be positive")
    masks = range(1 << n)
    horizontal = tuple(
        line_gap_count(bool(mask & (1 << column)) for column in range(n))
        for mask in masks
    )
    vertical_cache: dict[tuple[int, int], tuple[int, int]] = {}
    costs: dict[tuple[State, int], int] = {}
    parents: list[dict[tuple[State, int], tuple[State, int] | None]] = [{}]
    for mask in masks:
        forest = first_row_state(n, mask)
        if forest is None:
            continue
        packed, vertical_gain = _vertical_step(n, 0, mask)
        key = forest, packed
        costs[key] = 3 * mask.bit_count() + 2 * (horizontal[mask] + vertical_gain)
        parents[0][key] = None
    layer_states = [len(costs)]
    for _row in range(1, n):
        next_costs: dict[tuple[State, int], int] = {}
        next_parents: dict[tuple[State, int], tuple[State, int] | None] = {}
        for key, old_cost in costs.items():
            forest, packed = key
            for mask in masks:
                next_forest = transition(n, forest, mask)
                if next_forest is None:
                    continue
                vertical_key = packed, mask
                vertical = vertical_cache.get(vertical_key)
                if vertical is None:
                    vertical = _vertical_step(n, packed, mask)
                    vertical_cache[vertical_key] = vertical
                next_packed, vertical_gain = vertical
                next_key = next_forest, next_packed
                value = old_cost + 3 * mask.bit_count() + 2 * (
                    horizontal[mask] + vertical_gain
                )
                if value > next_costs.get(next_key, -1):
                    next_costs[next_key] = value
                    next_parents[next_key] = key
        costs = next_costs
        parents.append(next_parents)
        layer_states.append(len(costs))
    final = max(costs, key=costs.__getitem__)
    maximum = costs[final]
    rows = [0] * n
    key: tuple[State, int] | None = final
    for row in range(n - 1, -1, -1):
        assert key is not None
        rows[row] = key[0].forced_mask
        key = parents[row][key]
    witness = tuple(rows)
    if not is_forced_forest(n, list(witness)) or score(n, witness) != maximum:
        raise AssertionError("weighted grammar witness failed independent replay")
    gaps = local_gap_count(n, witness)
    if gaps != component_gap_count(n, witness):
        raise AssertionError("local and component gap definitions disagree")
    bound = n * n + 3 * n - 4
    return ExactMaximum(
        n, maximum, bound, bound - maximum,
        sum(mask.bit_count() for mask in witness), gaps, witness, tuple(layer_states)
    )


def maximal_sets(n: int) -> Iterator[tuple[int, ...]]:
    """Enumerate every inclusion-maximal acyclic set via the exact row grammar."""
    for rows in acyclic_row_sets(n):
        if is_inclusion_maximal(n, rows):
            yield rows


def maximal_census(n: int) -> dict:
    started = time.perf_counter()
    count = 0
    margins: Counter[int] = Counter()
    minimum = None
    witness = None
    for rows in maximal_sets(n):
        count += 1
        value = margin(n, rows)
        margins[value] += 1
        if minimum is None or value < minimum:
            minimum, witness = value, rows
    return {
        "n": n,
        "coverage": "all inclusion-maximal forced-acyclic sets",
        "count": count,
        "minimum_margin": minimum,
        "margin_distribution": dict(sorted(margins.items())),
        "worst_rows": list(witness) if witness is not None else None,
        "seconds": round(time.perf_counter() - started, 3),
    }


def _maximalize(n: int, rows: tuple[int, ...], rng: random.Random) -> tuple[int, ...]:
    rows = list(rows)
    candidates = [(row, column) for row in range(n) for column in range(n)]
    rng.shuffle(candidates)
    changed = True
    while changed:
        changed = False
        for row, column in candidates:
            if rows[row] & (1 << column):
                continue
            proposal = rows.copy()
            proposal[row] |= 1 << column
            if is_forced_forest(n, proposal):
                rows = proposal
                changed = True
    return tuple(rows)


KNOWN_ADVERSARIAL_SEEDS = {
    10: (957, 1, 585, 585, 585, 585, 585, 585, 512, 631),
}


def adversarial_mutations(n: int, attempts: int, seed: int) -> dict:
    """Remove 1--3 vertices, then greedily regrow while minimizing the margin."""
    rng = random.Random(seed)
    initial = KNOWN_ADVERSARIAL_SEEDS.get(n, _maximalize(n, canonical_rows(n), rng))
    if not is_forced_forest(n, list(initial)) or not is_inclusion_maximal(n, initial):
        raise AssertionError("adversarial seed is not an inclusion-maximal forced forest")
    current = initial
    best = current
    seen = {current}
    accepted = 0
    for _ in range(attempts):
        forced = [(r, c) for r in range(n) for c in range(n) if current[r] & (1 << c)]
        proposal = list(current)
        for row, column in rng.sample(forced, min(len(forced), rng.randint(1, 3))):
            proposal[row] &= ~(1 << column)
        candidate = _maximalize(n, tuple(proposal), rng)
        if candidate in seen:
            continue
        seen.add(candidate)
        delta = margin(n, candidate) - margin(n, current)
        if delta <= 0 or rng.random() < 0.03:
            current = candidate
            accepted += 1
        if margin(n, candidate) < margin(n, best):
            best = candidate
    gaps = local_gap_count(n, best)
    if gaps != component_gap_count(n, best):
        raise AssertionError("mutation winner failed independent gap replay")
    return {
        "n": n,
        "attempts": attempts,
        "distinct": len(seen),
        "accepted": accepted,
        "minimum_margin": margin(n, best),
        "score": score(n, best),
        "forced_count": sum(mask.bit_count() for mask in best),
        "gaps": gaps,
        "inclusion_maximal": is_inclusion_maximal(n, best),
        "rows": list(best),
    }


def build_report(exact_through: int, maximal_n: int, mutation_through: int, attempts: int) -> dict:
    exact = [exact_maximum_score(n).__dict__ for n in range(2, exact_through + 1)]
    census = maximal_census(maximal_n) if maximal_n else None
    mutations = [
        adversarial_mutations(n, attempts, 1_000_003 + 97 * n)
        for n in range(max(2, exact_through + 1), mutation_through + 1)
    ]
    margins = [item["margin"] for item in exact] + [item["minimum_margin"] for item in mutations]
    return {
        "scope": "finite computational evidence only; no Lean proof claim",
        "g_definition": (
            "sum over rows and columns of adjacent maximal F-run pairs whose two runs "
            "both have length at least two; singleton runs are not skipped"
        ),
        "inequality": "3|F|+2g(F) <= n^2+3n-4",
        "counterexample": next((item for item in exact if item["margin"] < 0), None)
        or next((item for item in mutations if item["minimum_margin"] < 0), None),
        "minimum_observed_margin": min(margins),
        "exact_maxima": exact,
        "maximal_census": census,
        "adversarial_mutations": mutations,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--exact-through",
        type=int,
        default=7,
        help="readable reference engine; use the Rust binary for exact n=8..10",
    )
    parser.add_argument("--maximal-n", type=int, default=6)
    parser.add_argument("--mutation-through", type=int, default=20)
    parser.add_argument("--attempts", type=int, default=2000)
    args = parser.parse_args()
    report = build_report(args.exact_through, args.maximal_n, args.mutation_through, args.attempts)
    print(json.dumps(report, indent=2, sort_keys=True))
    if report["counterexample"] is not None:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
