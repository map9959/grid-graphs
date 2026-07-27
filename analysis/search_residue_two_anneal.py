#!/usr/bin/env python3
"""Exact-cardinality stochastic repair of residue-two n=17 near-hits."""

from __future__ import annotations

import argparse
import math
import random

from construction_lab import run_check
from search_residue_anneal import (
    bits_to_rows,
    bridge_additions,
    dual_metrics,
    rows_to_bits,
    u_degree,
)
from search_residue_two_near import NEAR_MACRO, NEAR_PHASECROP, NEAR_PUMP


def energy(metrics) -> int:
    return (
        10_000 * (metrics.components - 1)
        + 30 * (metrics.total_faces - metrics.out_size)
        + 2 * abs(metrics.cycle_excess - 1)
    )


def weighted_sample(
    pool: list[int], weights: list[float], count: int, rng: random.Random
) -> list[int]:
    pool = list(pool)
    weights = list(weights)
    selected = []
    for _ in range(min(count, len(pool))):
        threshold = rng.random() * sum(weights)
        total = 0.0
        index = 0
        for index, weight in enumerate(weights):
            total += weight
            if total >= threshold:
                break
        selected.append(pool.pop(index))
        weights.pop(index)
    return selected


def propose(bits: int, n: int, metrics, rng: random.Random) -> int:
    us = [vertex for vertex in range(n * n) if bits & (1 << vertex)]
    dots = [vertex for vertex in range(n * n) if not bits & (1 << vertex)]
    if metrics.components > 1 and rng.random() < 0.8:
        options = bridge_additions(bits, n, metrics)
        if options:
            additions = list(rng.choice(options))
            if len(additions) == 1:
                anchor_row, anchor_column = divmod(additions[0], n)
                nearby = [
                    vertex
                    for vertex in dots
                    if vertex not in additions
                    and abs(vertex // n - anchor_row)
                    + abs(vertex % n - anchor_column)
                    <= 5
                ]
                roll = rng.random()
                extra_count = 1 if roll < 0.15 else 2 if roll < 0.75 else 3
                source = nearby if len(nearby) >= extra_count and rng.random() < 0.7 else dots
                source = [vertex for vertex in source if vertex not in additions]
                additions.extend(rng.sample(source, min(extra_count, len(source))))
            elif len(additions) == 2 and rng.random() < 0.65:
                additions.append(rng.choice([v for v in dots if v not in additions]))

            pool = [vertex for vertex in us if vertex not in additions]
            weights = [(5 - u_degree(bits, n, vertex)) ** 4 for vertex in pool]
            removals = weighted_sample(pool, weights, len(additions), rng)
            child = bits
            for vertex in additions:
                child |= 1 << vertex
            for vertex in removals:
                child &= ~(1 << vertex)
            return child

    roll = rng.random()
    count = 1 if roll < 0.35 else 2 if roll < 0.62 else 3 if roll < 0.84 else 4 if roll < 0.96 else 5
    removals = rng.sample(us, count)
    if rng.random() < 0.7:
        local = [
            vertex
            for vertex in dots
            if min(
                abs(vertex // n - removed // n) + abs(vertex % n - removed % n)
                for removed in removals
            )
            <= 5
        ]
        additions = rng.sample(local, count) if len(local) >= count else rng.sample(dots, count)
    else:
        additions = rng.sample(dots, count)
    child = bits
    for vertex in removals:
        child &= ~(1 << vertex)
    for vertex in additions:
        child |= 1 << vertex
    return child


def search(candidate: str, seed: int, steps: int, report_every: int) -> int:
    rows = {
        "phasecrop": NEAR_PHASECROP,
        "pump": NEAR_PUMP,
        "macro": NEAR_MACRO,
    }[candidate]
    n = len(rows)
    rng = random.Random(seed)
    bits = rows_to_bits(rows)
    metrics = dual_metrics(bits, n)
    current_energy = energy(metrics)
    best_bits = bits
    best_metrics = metrics
    accepted = 0

    for step in range(1, steps + 1):
        if step > 1 and step % 60_000 == 1:
            bits = best_bits
            us = [vertex for vertex in range(n * n) if bits & (1 << vertex)]
            dots = [vertex for vertex in range(n * n) if not bits & (1 << vertex)]
            for vertex in rng.sample(us, 8):
                bits &= ~(1 << vertex)
            for vertex in rng.sample(dots, 8):
                bits |= 1 << vertex
            metrics = dual_metrics(bits, n)
            current_energy = energy(metrics)
        child = propose(bits, n, metrics, rng)
        child_metrics = dual_metrics(child, n)
        child_energy = energy(child_metrics)
        phase = (step % 60_000) / 60_000
        temperature = 2_500 * (1 - phase) + 25
        if child_energy <= current_energy or rng.random() < math.exp(
            max(-50.0, (current_energy - child_energy) / temperature)
        ):
            bits = child
            metrics = child_metrics
            current_energy = child_energy
            accepted += 1
        if metrics.score < best_metrics.score:
            best_bits = bits
            best_metrics = metrics
            print(
                f"improved candidate={candidate} seed={seed} step={step} "
                f"score={metrics.score} edges={metrics.edge_count}",
                flush=True,
            )
        if metrics.components == 1:
            result = bits_to_rows(bits, n)
            if run_check(n, result, verbose=True)["all_ok"]:
                print(
                    f"found candidate={candidate} seed={seed} step={step} "
                    f"accepted={accepted}",
                    flush=True,
                )
                print("\n".join(result), flush=True)
                return 0
        if report_every and step % report_every == 0:
            print(
                f"progress candidate={candidate} seed={seed} step={step} "
                f"current={metrics.score} best={best_metrics.score} accepted={accepted}",
                flush=True,
            )

    print(
        f"result candidate={candidate} seed={seed} steps={steps} "
        f"accepted={accepted} best={best_metrics.score} edges={best_metrics.edge_count}",
        flush=True,
    )
    print("\n".join(bits_to_rows(best_bits, n)), flush=True)
    return 1


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--candidate", choices=("phasecrop", "pump", "macro"), required=True
    )
    parser.add_argument("--seed", type=int, required=True)
    parser.add_argument("--steps", type=int, default=500_000)
    parser.add_argument("--report-every", type=int, default=0)
    args = parser.parse_args()
    raise SystemExit(search(args.candidate, args.seed, args.steps, args.report_every))


if __name__ == "__main__":
    main()
