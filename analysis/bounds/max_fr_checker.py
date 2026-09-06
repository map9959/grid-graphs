#!/usr/bin/env python3
"""Finite falsification gate for Max-FR and the direct balanced-crop property.

This mirrors the corner embeddings in FourCropSurgery.lean.  Repair rank is
computed exactly as a maximum forced-forest extension of the cropped set; this
is the bundled rank rho from FOUR_CROP_SIMULTANEOUS_REPAIR_RANK.md, not the
ordinary rank of individually selectable omitted edges.

All results are finite computations and are not Lean proof claims.
"""

from __future__ import annotations

import argparse
from collections import Counter
import json
import random
import time
from dataclasses import asdict, dataclass
from functools import lru_cache

from typing import Iterable, Iterator

from analysis.patterns.diagonal_patterns import (
    residue_one_pattern,
    residue_two_pattern,
    residue_zero_explicit_pattern,
)
from analysis.bounds.forced_forest_row_grammar import (
    State,
    first_row_state,
    is_forced_forest,
    transition,
)
from analysis._paths import REPO_ROOT

CORNERS = ("NW", "NE", "SW", "SE")


@dataclass(frozen=True)
class CornerResult:
    corner: str
    loss: int
    demand: int
    repair_rank: int
    balanced: bool


@dataclass(frozen=True)
class CheckResult:
    n: int
    forced_count: int
    corners: tuple[CornerResult, ...]
    signed_rhs: int
    positive_rhs: int
    rank_sum: int
    max_fr: bool
    positive_fr: bool
    min_corner_frame_loss: int
    min_loss_minus_2n: int
    minimum_repair_rank_needed: int
    minimum_loss_crop_balanced: bool
    some_crop_balanced: bool


def crop_rows(n: int, rows: tuple[int, ...], corner: str) -> tuple[int, ...]:
    """Apply fourCropEmbedding: offsets are independently zero or three."""
    if n < 3 or corner not in CORNERS or len(rows) != n:
        raise ValueError("invalid four-crop input")
    size = n - 3
    row_offset = 0 if corner[0] == "N" else 3
    col_offset = 0 if corner[1] == "W" else 3
    mask = (1 << size) - 1
    return tuple((rows[r + row_offset] >> col_offset) & mask for r in range(size))


@lru_cache(maxsize=None)
def maximum_repair_rank(mandatory_rows: tuple[int, ...]) -> int:
    """Exact maximum |R| over disjoint admissible repairs of a square crop."""
    m = len(mandatory_rows)
    if m == 0:
        return 0
    limit = 1 << m
    if any(mask < 0 or mask >= limit for mask in mandatory_rows):
        raise ValueError("mandatory row does not fit crop")

    costs: dict[State, int] = {}
    mandatory = mandatory_rows[0]
    for mask in range(limit):
        if mask & mandatory != mandatory:
            continue
        state = first_row_state(m, mask)
        if state is not None:
            costs[state] = (mask ^ mandatory).bit_count()
    for row in range(1, m):
        mandatory = mandatory_rows[row]
        next_costs: dict[State, int] = {}
        for state, cost in costs.items():
            for mask in range(limit):
                if mask & mandatory != mandatory:
                    continue
                next_state = transition(m, state, mask)
                if next_state is None:
                    continue
                value = cost + (mask ^ mandatory).bit_count()
                if value > next_costs.get(next_state, -1):
                    next_costs[next_state] = value
        costs = next_costs
    if not costs:
        raise AssertionError("an acyclic crop must admit its empty repair")
    return max(costs.values())


def check_max_fr(n: int, rows: Iterable[int]) -> CheckResult:
    rows = tuple(rows)
    if n < 3 or len(rows) != n or not is_forced_forest(n, list(rows)):
        raise ValueError("input must be a forced-acyclic n by n set with n >= 3")
    forced_count = sum(mask.bit_count() for mask in rows)
    corner_results = []
    for corner in CORNERS:
        cropped = crop_rows(n, rows, corner)
        loss = forced_count - sum(mask.bit_count() for mask in cropped)
        rank = maximum_repair_rank(cropped)
        demand = max(0, loss - 2 * n)
        corner_results.append(
            CornerResult(corner, loss, demand, rank, rank >= loss - 2 * n)
        )
    signed_rhs = sum(item.loss - 2 * n for item in corner_results)
    positive_rhs = sum(item.demand for item in corner_results)
    rank_sum = sum(item.repair_rank for item in corner_results)
    min_loss = min(item.loss for item in corner_results)
    minimum_loss_crops = [item for item in corner_results if item.loss == min_loss]
    return CheckResult(
        n=n,
        forced_count=forced_count,
        corners=tuple(corner_results),
        signed_rhs=signed_rhs,
        positive_rhs=positive_rhs,
        rank_sum=rank_sum,
        max_fr=rank_sum >= signed_rhs,
        positive_fr=rank_sum >= positive_rhs,
        min_corner_frame_loss=min_loss,
        min_loss_minus_2n=min_loss - 2 * n,
        minimum_repair_rank_needed=max(0, min_loss - 2 * n),
        minimum_loss_crop_balanced=any(item.balanced for item in minimum_loss_crops),
        some_crop_balanced=any(item.balanced for item in corner_results),
    )


def exact_maximum(n: int) -> int:
    path = REPO_ROOT / "data" / "diagonal.csv"
    # The historical header contains the unquoted field name ``P(n,n)``.
    for line in path.read_text().splitlines()[1:]:
        fields = line.split(",")
        if int(fields[0]) == n and "lower bound" not in fields[-1]:
            return int(fields[1])
    raise KeyError(f"no exact maximum recorded for n={n}")


def maximum_witnesses(n: int, limit: int | None = None) -> Iterator[tuple[int, ...]]:
    """Enumerate distinct row sequences attaining the exact frontier-DP max."""
    if n <= 0:
        return
    masks = range(1 << n)

    @lru_cache(maxsize=None)
    def suffix(row: int, state: State) -> int:
        if row == n:
            return 0
        best = -1
        for mask in masks:
            next_state = transition(n, state, mask)
            if next_state is not None:
                best = max(best, mask.bit_count() + suffix(row + 1, next_state))
        return best

    target = exact_maximum(n)
    emitted = 0

    def extend(row: int, state: State, prefix: tuple[int, ...], score: int):
        nonlocal emitted
        if limit is not None and emitted >= limit:
            return
        if row == n:
            if score == target:
                emitted += 1
                yield prefix
            return
        for mask in masks:
            next_state = transition(n, state, mask)
            if next_state is None:
                continue
            value = mask.bit_count()
            if score + value + suffix(row + 1, next_state) == target:
                yield from extend(row + 1, next_state, prefix + (mask,), score + value)

    for mask in masks:
        state = first_row_state(n, mask)
        if state is None or mask.bit_count() + suffix(1, state) != target:
            continue
        yield from extend(1, state, (mask,), mask.bit_count())
        if limit is not None and emitted >= limit:
            return


def canonical_witness(n: int) -> tuple[int, ...]:
    if n % 3 == 0:
        pattern = residue_zero_explicit_pattern(n)
    elif n % 3 == 1:
        pattern = residue_one_pattern(n)
    else:
        pattern = residue_two_pattern(n)
    rows = tuple(sum((ch == ".") << c for c, ch in enumerate(row)) for row in pattern)
    if sum(mask.bit_count() for mask in rows) != exact_maximum(n):
        raise AssertionError("canonical witness does not have recorded maximum size")
    return rows


def transform(rows: tuple[int, ...], rotation: int, reflect: bool) -> tuple[int, ...]:
    n = len(rows)
    points = {(r, c) for r, mask in enumerate(rows) for c in range(n) if mask >> c & 1}
    for _ in range(rotation):
        points = {(c, n - 1 - r) for r, c in points}
    if reflect:
        points = {(r, n - 1 - c) for r, c in points}
    return tuple(sum(1 << c for rr, c in points if rr == r) for r in range(n))


def random_maximum_witnesses(
    seed_rows: tuple[int, ...], count: int, seed: int
) -> Iterator[tuple[int, ...]]:
    """Random cardinality-preserving exchanges from a certified maximum seed."""
    rng = random.Random(seed)
    n = len(seed_rows)
    current = list(seed_rows)
    seen = {tuple(current)}
    attempts = 0
    while len(seen) <= count and attempts < max(1000, count * 500):
        attempts += 1
        forced = [(r, c) for r in range(n) for c in range(n) if current[r] >> c & 1]
        unforced = [(r, c) for r in range(n) for c in range(n) if not current[r] >> c & 1]
        remove = rng.choice(forced)
        add = rng.choice(unforced)
        candidate = current.copy()
        candidate[remove[0]] &= ~(1 << remove[1])
        candidate[add[0]] |= 1 << add[1]
        if is_forced_forest(n, candidate):
            current = candidate
            key = tuple(current)
            if key not in seen:
                seen.add(key)
                yield key


TARGETED_MAXIMUM_WITNESSES = {
    9: (
        (509, 1, 65, 285, 257, 353, 265, 257, 381),
        (383, 256, 292, 293, 289, 265, 329, 256, 319),
        (509, 1, 65, 285, 257, 369, 261, 1, 505),
    ),
}


def balance_search_witnesses(
    seed_rows: tuple[int, ...], count: int, seed: int
) -> Iterator[tuple[int, ...]]:
    """Bias exact maximum exchanges toward failure of every crop balance test."""
    rng = random.Random(seed)
    n = len(seed_rows)
    current = seed_rows
    current_score = max(
        item.repair_rank - item.demand for item in check_max_fr(n, current).corners
    )
    emitted = 0
    attempts = 0
    seen = {current}
    while emitted < count and attempts < max(2000, count * 1000):
        attempts += 1
        forced = [(r, c) for r in range(n) for c in range(n) if current[r] >> c & 1]
        unforced = [(r, c) for r in range(n) for c in range(n) if not current[r] >> c & 1]
        remove = rng.choice(forced)
        add = rng.choice(unforced)
        candidate = list(current)
        candidate[remove[0]] &= ~(1 << remove[1])
        candidate[add[0]] |= 1 << add[1]
        key = tuple(candidate)
        if key in seen or not is_forced_forest(n, candidate):
            continue
        seen.add(key)
        result = check_max_fr(n, key)
        score = max(item.repair_rank - item.demand for item in result.corners)
        # Keep pressure on the best obstruction while allowing occasional escapes.
        if score <= current_score or rng.random() < 0.08:
            current = key
            current_score = score
        emitted += 1
        yield key


def _distribution(values: Iterable[int]) -> dict[str, int]:
    return {str(value): count for value, count in sorted(Counter(values).items())}


def summarize_results(n: int, kind: str, results: list[CheckResult]) -> dict:
    """Aggregate every requested per-witness diagnostic without hiding failures."""
    if not results:
        return {"n": n, "kind": kind, "checked": 0}
    return {
        "n": n,
        "kind": kind,
        "checked": len(results),
        "min_corner_frame_loss": min(item.min_corner_frame_loss for item in results),
        "min_corner_frame_loss_distribution": _distribution(
            item.min_corner_frame_loss for item in results
        ),
        "min_loss_minus_2n_distribution": _distribution(
            item.min_loss_minus_2n for item in results
        ),
        "minimum_repair_rank_needed": max(
            item.minimum_repair_rank_needed for item in results
        ),
        "minimum_repair_rank_needed_distribution": _distribution(
            item.minimum_repair_rank_needed for item in results
        ),
        "minimum_loss_crop_balanced": all(
            item.minimum_loss_crop_balanced for item in results
        ),
        "minimum_loss_crop_balanced_distribution": {
            str(value).lower(): count
            for value, count in sorted(
                Counter(item.minimum_loss_crop_balanced for item in results).items()
            )
        },
        "some_crop_balanced": all(item.some_crop_balanced for item in results),
        "some_crop_balanced_distribution": {
            str(value).lower(): count
            for value, count in sorted(
                Counter(item.some_crop_balanced for item in results).items()
            )
        },
        "max_fr": all(item.max_fr for item in results),
        "minimum_signed_margin": min(item.rank_sum - item.signed_rhs for item in results),
    }


def targeted_witnesses(n: int, random_count: int) -> set[tuple[int, ...]]:
    seeds = {canonical_witness(n), *TARGETED_MAXIMUM_WITNESSES.get(n, ())}
    witnesses = {
        transform(rows, rotation, reflect)
        for rows in seeds
        for rotation in range(4)
        for reflect in (False, True)
    }
    per_seed = max(0, random_count // len(seeds))
    for index, rows in enumerate(sorted(seeds)):
        witnesses.update(random_maximum_witnesses(rows, per_seed, 104729 + 97 * n + index))
        witnesses.update(balance_search_witnesses(rows, per_seed, 130363 + 97 * n + index))
    return witnesses


def run_gate(exhaustive_max_n: int, exhaustive_limit: int | None, random_count: int) -> dict:
    started = time.perf_counter()
    records = []
    max_fr_counterexample = None
    balanced_crop_counterexample = None
    exhaustive_max_n = min(exhaustive_max_n, 9)
    for n in range(3, 10):
        kind = "exhaustive" if n <= exhaustive_max_n else "targeted_random"
        witnesses = (
            maximum_witnesses(n, exhaustive_limit)
            if kind == "exhaustive"
            else sorted(targeted_witnesses(n, random_count))
        )
        results = []
        for rows in witnesses:
            result = check_max_fr(n, rows)
            results.append(result)
            witness = {"rows": list(rows), "result": asdict(result)}
            if not result.max_fr and max_fr_counterexample is None:
                max_fr_counterexample = witness
            if not result.some_crop_balanced and balanced_crop_counterexample is None:
                balanced_crop_counterexample = witness
        records.append(summarize_results(n, kind, results))
    return {
        "scope": "finite computational falsification only; no Lean proof claim",
        "records": records,
        "max_fr_counterexample": max_fr_counterexample,
        "balanced_crop_counterexample": balanced_crop_counterexample,
        "repair_rank_cache": asdict_cache(maximum_repair_rank.cache_info()),
        "seconds": round(time.perf_counter() - started, 3),
    }


def asdict_cache(info) -> dict:
    return {name: getattr(info, name) for name in ("hits", "misses", "maxsize", "currsize")}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exhaustive-max-n", type=int, default=6)
    parser.add_argument("--exhaustive-limit", type=int)
    parser.add_argument("--random-count", type=int, default=100)
    args = parser.parse_args()
    report = run_gate(args.exhaustive_max_n, args.exhaustive_limit, args.random_count)
    print(json.dumps(report, indent=2))
    if report["balanced_crop_counterexample"] is not None:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
