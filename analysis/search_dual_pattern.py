#!/usr/bin/env python3
"""Heuristic search for target-size U patterns with connected dual graph.

This is construction-discovery tooling, not proof. It searches directly in the
space of U-sets of the conjectured cardinality and tries to maximize the number
of dual faces connected to OUT.
"""

from __future__ import annotations

import argparse
import random

from diagonal_patterns import q_formula


def dual_connected_count(n: int, U: set[tuple[int, int]]) -> tuple[int, int]:
    faces = ["OUT"] + [(r, c) for r in range(n - 1) for c in range(n - 1)]
    parent = {x: x for x in faces}

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(a, b):
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[rb] = ra

    def dh(r, c):
        if r == 0:
            return "OUT", (0, c)
        if r == n - 1:
            return "OUT", (n - 2, c)
        return (r - 1, c), (r, c)

    def dv(r, c):
        if c == 0:
            return "OUT", (r, 0)
        if c == n - 1:
            return "OUT", (r, n - 2)
        return (r, c - 1), (r, c)

    for r in range(n):
        for c in range(n - 1):
            if (r, c) in U and (r, c + 1) in U:
                union(*dh(r, c))
    for r in range(n - 1):
        for c in range(n):
            if (r, c) in U and (r + 1, c) in U:
                union(*dv(r, c))
    root = find("OUT")
    return sum(1 for f in faces if find(f) == root), len(faces)


def initial_pattern(n: int) -> set[tuple[int, int]]:
    # Dense two-out-of-three row baseline, then sample down/up to target.
    target = q_formula(n)
    U = {(r, c) for r in range(n) for c in range(n) if r % 3 in (1, 2)}
    cells = [(r, c) for r in range(n) for c in range(n)]
    if len(U) > target:
        for x in random.sample(list(U), len(U) - target):
            U.remove(x)
    elif len(U) < target:
        avail = [x for x in cells if x not in U]
        for x in random.sample(avail, target - len(U)):
            U.add(x)
    return U


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("n", type=int)
    parser.add_argument("--restarts", type=int, default=50)
    parser.add_argument("--steps", type=int, default=20000)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    random.seed(args.seed)
    n = args.n
    target = q_formula(n)
    cells = [(r, c) for r in range(n) for c in range(n)]
    best_U: set[tuple[int, int]] | None = None
    best_score = -1
    total_faces = (n - 1) * (n - 1) + 1
    for restart in range(args.restarts):
        U = initial_pattern(n)
        score, _ = dual_connected_count(n, U)
        temp = 3.0
        for step in range(args.steps):
            if score == total_faces:
                break
            a = random.choice(tuple(U))
            b = random.choice(cells)
            if b in U:
                continue
            U.remove(a)
            U.add(b)
            ns, _ = dual_connected_count(n, U)
            accept = ns >= score or random.random() < pow(2.718281828, (ns - score) / max(temp, 0.01))
            if accept:
                score = ns
            else:
                U.remove(b)
                U.add(a)
            temp *= 0.9995
        if score > best_score:
            best_score = score
            best_U = set(U)
            print(f"# restart={restart} best={best_score}/{total_faces}")
        if best_score == total_faces:
            break
    assert best_U is not None
    print(f"# n={n} |U|={len(best_U)} target={target} connected={best_score == total_faces} score={best_score}/{total_faces}")
    for r in range(n):
        print("".join("U" if (r, c) in best_U else "." for c in range(n)))


if __name__ == "__main__":
    main()
