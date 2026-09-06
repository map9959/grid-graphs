#!/usr/bin/env python3
"""Exact-cardinality stochastic search for diagonal residue constructions."""

from __future__ import annotations

import argparse
import math
import random
from dataclasses import dataclass

from analysis.patterns.construction_lab import q_formula, run_check
from analysis.patterns.diagonal_patterns import (
    residue_one_pattern,
    residue_zero_explicit_pattern,
    residue_zero_improved_pattern,
)
from analysis.transport.search_band_pump import Pump, pump_pattern


NEAR_N21 = [
    ".............UU......",
    "UUUUUUUUUUUUUUUUUUUUU",
    ".UU.UU.UU.UU.U.UU.UU.",
    ".UU.UU.UU.UUUU.UU.UU.",
    ".UU.UU.UUUU.UU.UU.UU.",
    ".UU.UU.U.UU.UU.UU.UU.",
    ".UU.UUUU.UU.UU.UU.UU.",
    ".UUUU.UU.UU.UU.UU.UU.",
    ".U.UU.UU.UU.UU.UU.UU.",
    ".UUUU.UU.UU.UU.UU.UU.",
    ".UU.U.UU.UU.UU.UU.UU.",
    ".UU.UUUU.UU.UU.UU.UU.",
    ".UU.UU.UUUU.UU.UU.UU.",
    ".UU.UU.UU.U.UU.UU.UU.",
    ".UU.UU.UU.UUUU.UU.UU.",
    ".UU.UU.UU.UU.UUUU.UU.",
    ".UU.UU.UU.UU.UU.U.UU.",
    ".UU.UU.UU.UU.UU.UUUU.",
    ".UU.UU.UU.UU.UU.UU.U.",
    ".UUUUUUUUUUUUUUUUUUU.",
    "..................UU.",
]


@dataclass(frozen=True)
class DualMetrics:
    components: int
    out_size: int
    total_faces: int
    edge_count: int
    cycle_excess: int
    roots: tuple[int, ...]

    @property
    def score(self) -> tuple[int, int, int]:
        return (
            self.components - 1,
            self.total_faces - self.out_size,
            abs(self.cycle_excess - 1),
        )


def rows_to_bits(rows: list[str]) -> int:
    n = len(rows)
    return sum(
        1 << (r * n + c)
        for r, row in enumerate(rows)
        for c, value in enumerate(row)
        if value == "U"
    )


def bits_to_rows(bits: int, n: int) -> list[str]:
    return [
        "".join("U" if bits & (1 << (r * n + c)) else "." for c in range(n))
        for r in range(n)
    ]


def dual_metrics(bits: int, n: int) -> DualMetrics:
    side = n - 1
    total = side * side + 1
    parent = list(range(total))

    def find(value: int) -> int:
        while parent[value] != value:
            parent[value] = parent[parent[value]]
            value = parent[value]
        return value

    def union(left: int, right: int) -> None:
        left = find(left)
        right = find(right)
        if left != right:
            parent[right] = left

    def face(r: int, c: int) -> int:
        return 1 + r * side + c

    edges = 0
    for r in range(n):
        for c in range(side):
            left_vertex = r * n + c
            if bits & (1 << left_vertex) and bits & (1 << (left_vertex + 1)):
                edges += 1
                above = 0 if r == 0 else face(r - 1, c)
                below = 0 if r + 1 == n else face(r, c)
                union(above, below)
    for r in range(side):
        for c in range(n):
            top_vertex = r * n + c
            if bits & (1 << top_vertex) and bits & (1 << (top_vertex + n)):
                edges += 1
                left = 0 if c == 0 else face(r, c - 1)
                right = 0 if c + 1 == n else face(r, c)
                union(left, right)

    roots = tuple(find(value) for value in range(total))
    out_root = roots[0]
    components = len(set(roots))
    out_size = sum(root == out_root for root in roots)
    return DualMetrics(
        components,
        out_size,
        total,
        edges,
        edges - total + components,
        roots,
    )


def energy(metrics: DualMetrics) -> float:
    return (
        10_000 * (metrics.components - 1)
        + 30 * (metrics.total_faces - metrics.out_size)
        + 2 * abs(metrics.cycle_excess - 1)
    )


def transform(rows: list[str], choice: int) -> list[str]:
    out = list(rows)
    rotations = choice % 4
    reflected = choice >= 4
    for _ in range(rotations):
        out = ["".join(row[c] for row in reversed(out)) for c in range(len(out))]
    if reflected:
        out = [row[::-1] for row in out]
    return out


def adjust_cardinality(rows: list[str], target: int, rng: random.Random) -> list[str]:
    n = len(rows)
    cells = [list(row) for row in rows]
    us = [(r, c) for r in range(n) for c in range(n) if cells[r][c] == "U"]
    dots = [(r, c) for r in range(n) for c in range(n) if cells[r][c] == "."]
    while len(us) > target:
        r, c = us.pop(rng.randrange(len(us)))
        cells[r][c] = "."
        dots.append((r, c))
    while len(us) < target:
        index = rng.randrange(len(dots))
        r, c = dots.pop(index)
        cells[r][c] = "U"
        us.append((r, c))
    return ["".join(row) for row in cells]


def make_seed(family: str, seed: int) -> list[str]:
    rng = random.Random(seed ^ 0x5EED)
    if family == "near":
        return list(NEAR_N21)
    if family == "scaffold":
        rows = residue_zero_improved_pattern(21)
    elif family == "crop":
        source = residue_one_pattern(22)
        delete_row = (1, 0, 2, 21)[seed % 4]
        delete_col = (15, 9, 3, 18)[(seed // 4) % 4]
        rows = [
            "".join(value for c, value in enumerate(row) if c != delete_col)
            for r, row in enumerate(source)
            if r != delete_row
        ]
    elif family == "pump":
        pumps = (
            Pump(8, 7, 10, 10),
            Pump(8, 7, 11, 11),
            Pump(9, 7, 10, 10),
            Pump(10, 9, 10, 10),
        )
        rows = pump_pattern(residue_zero_explicit_pattern(18), pumps[seed % len(pumps)])
    else:
        raise ValueError(f"unknown seed family {family}")
    rows = transform(rows, (seed // 17) % 8)
    return adjust_cardinality(rows, q_formula(21), rng)


def u_degree(bits: int, n: int, vertex: int) -> int:
    r, c = divmod(vertex, n)
    neighbors = []
    if r:
        neighbors.append(vertex - n)
    if r + 1 < n:
        neighbors.append(vertex + n)
    if c:
        neighbors.append(vertex - 1)
    if c + 1 < n:
        neighbors.append(vertex + 1)
    return sum(bool(bits & (1 << neighbor)) for neighbor in neighbors)


def bridge_additions(bits: int, n: int, metrics: DualMetrics):
    side = n - 1

    def face(r: int, c: int) -> int:
        return 1 + r * side + c

    options = []
    for r in range(n):
        for c in range(side):
            a = 0 if r == 0 else face(r - 1, c)
            b = 0 if r + 1 == n else face(r, c)
            if metrics.roots[a] == metrics.roots[b]:
                continue
            vertices = (r * n + c, r * n + c + 1)
            missing = tuple(v for v in vertices if not bits & (1 << v))
            if missing:
                options.append(missing)
    for r in range(side):
        for c in range(n):
            a = 0 if c == 0 else face(r, c - 1)
            b = 0 if c + 1 == n else face(r, c)
            if metrics.roots[a] == metrics.roots[b]:
                continue
            vertices = (r * n + c, (r + 1) * n + c)
            missing = tuple(v for v in vertices if not bits & (1 << v))
            if missing:
                options.append(missing)
    return options


def choose_removals(
    bits: int, n: int, count: int, forbidden: set[int], rng: random.Random
) -> tuple[int, ...]:
    pool = [v for v in range(n * n) if bits & (1 << v) and v not in forbidden]
    if len(pool) < count:
        return ()
    sample = rng.sample(pool, min(len(pool), max(24, count * 8)))
    sample.sort(key=lambda vertex: (u_degree(bits, n, vertex), rng.random()))
    return tuple(sample[:count])


def propose(
    bits: int, n: int, metrics: DualMetrics, rng: random.Random
) -> int:
    if metrics.components > 1 and rng.random() < 0.55:
        options = bridge_additions(bits, n, metrics)
        if options:
            additions = tuple(rng.choice(options))
            if len(additions) == 1 and metrics.components == 2 and rng.random() < 0.8:
                anchor_r, anchor_c = divmod(additions[0], n)
                nearby = [
                    vertex
                    for vertex in range(n * n)
                    if not bits & (1 << vertex)
                    and vertex not in additions
                    and abs(vertex // n - anchor_r) + abs(vertex % n - anchor_c) <= 3
                ]
                if nearby:
                    extra_count = 2 if rng.random() < 0.45 and len(nearby) >= 2 else 1
                    additions = (*additions, *rng.sample(nearby, extra_count))
            removals = choose_removals(bits, n, len(additions), set(additions), rng)
            if removals:
                child = bits
                for vertex in additions:
                    child |= 1 << vertex
                for vertex in removals:
                    child &= ~(1 << vertex)
                return child

    count = 1 if rng.random() < 0.65 else 2 if rng.random() < 0.85 else 3
    us = [v for v in range(n * n) if bits & (1 << v)]
    dots = [v for v in range(n * n) if not bits & (1 << v)]
    removals = rng.sample(us, count)
    additions = rng.sample(dots, count)
    child = bits
    for vertex in removals:
        child &= ~(1 << vertex)
    for vertex in additions:
        child |= 1 << vertex
    return child


def search(family: str, seed: int, steps: int, report_every: int):
    n = 21
    rng = random.Random(seed)
    rows = make_seed(family, seed)
    bits = rows_to_bits(rows)
    metrics = dual_metrics(bits, n)
    current_energy = energy(metrics)
    best_bits = bits
    best_metrics = metrics
    accepted = 0

    for step in range(1, steps + 1):
        child = propose(bits, n, metrics, rng)
        child_metrics = dual_metrics(child, n)
        child_energy = energy(child_metrics)
        phase = (step % 50_000) / 50_000
        temperature = 2_500 * (1 - phase) + 25
        if child_energy <= current_energy or rng.random() < math.exp(
            min(0.0, (current_energy - child_energy) / temperature)
        ):
            bits = child
            metrics = child_metrics
            current_energy = child_energy
            accepted += 1
        if metrics.score < best_metrics.score:
            best_bits = bits
            best_metrics = metrics
            print(
                f"improved family={family} seed={seed} step={step} "
                f"score={best_metrics.score} edges={best_metrics.edge_count}"
            )
        if best_metrics.components == 1:
            candidate = bits_to_rows(best_bits, n)
            info = run_check(n, candidate, verbose=True)
            if info["all_ok"]:
                return candidate, best_metrics, step, accepted
        if report_every and step % report_every == 0:
            print(
                f"progress family={family} seed={seed} step={step} "
                f"current={metrics.score} best={best_metrics.score} accepted={accepted}"
            )
    return bits_to_rows(best_bits, n), best_metrics, steps, accepted


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--family", choices=("pump", "scaffold", "crop", "near"), default="pump"
    )
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--steps", type=int, default=250_000)
    parser.add_argument("--report-every", type=int, default=50_000)
    parser.add_argument("--print-best", action="store_true")
    args = parser.parse_args()
    best_rows, metrics, steps, accepted = search(
        args.family, args.seed, args.steps, args.report_every
    )
    print(
        f"result family={args.family} seed={args.seed} steps={steps} "
        f"accepted={accepted} best={metrics.score} edges={metrics.edge_count}"
    )
    info = run_check(21, best_rows)
    if info["all_ok"] or args.print_best:
        print("\n".join(best_rows))
    if not info["all_ok"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
