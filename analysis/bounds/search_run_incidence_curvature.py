#!/usr/bin/env python3
"""Search complements of grid spanning trees for small run-incidence curvature."""

from __future__ import annotations

import argparse
import random
import subprocess
from collections import defaultdict, deque

Edge = tuple[int, int]
Face = tuple[int, int] | str


def grid_and_dual_edges(n: int) -> tuple[list[Edge], list[tuple[Face, Face]]]:
    primal: list[Edge] = []
    dual: list[tuple[Face, Face]] = []
    for r in range(n):
        for c in range(n - 1):
            primal.append((r * n + c, r * n + c + 1))
            if r == 0:
                dual.append(("OUT", (0, c)))
            elif r == n - 1:
                dual.append(((n - 2, c), "OUT"))
            else:
                dual.append(((r - 1, c), (r, c)))
    for r in range(n - 1):
        for c in range(n):
            primal.append((r * n + c, (r + 1) * n + c))
            if c == 0:
                dual.append(("OUT", (r, 0)))
            elif c == n - 1:
                dual.append(((r, n - 2), "OUT"))
            else:
                dual.append(((r, c - 1), (r, c)))
    return primal, dual


def random_dual_tree(n: int, dual: list[tuple[Face, Face]], rng: random.Random) -> set[int]:
    faces: list[Face] = ["OUT", *((r, c) for r in range(n - 1) for c in range(n - 1))]
    parent = {face: face for face in faces}

    def root(face: Face) -> Face:
        while parent[face] != face:
            parent[face] = parent[parent[face]]
            face = parent[face]
        return face

    order = list(range(len(dual)))
    rng.shuffle(order)
    tree: set[int] = set()
    for index in order:
        left, right = dual[index]
        left_root, right_root = root(left), root(right)
        if left_root != right_root:
            parent[left_root] = right_root
            tree.add(index)
    return tree


def component_data(n: int, primal: list[Edge], tree: set[int]) -> list[tuple[list[int], int, int]]:
    adjacency: dict[int, list[int]] = defaultdict(list)
    for index in tree:
        left, right = primal[index]
        adjacency[left].append(right)
        adjacency[right].append(left)
    unseen = set(adjacency)
    result: list[tuple[list[int], int, int]] = []
    while unseen:
        start = min(unseen)
        stack = [start]
        unseen.remove(start)
        vertices: list[int] = []
        degree_sum = 0
        while stack:
            vertex = stack.pop()
            vertices.append(vertex)
            degree_sum += len(adjacency[vertex])
            for neighbor in adjacency[vertex]:
                if neighbor in unseen:
                    unseen.remove(neighbor)
                    stack.append(neighbor)
        edges = degree_sum // 2
        beta = edges - len(vertices) + 1
        result.append((sorted(vertices), edges, beta))
    result.sort()
    return result


def curvature(n: int, primal: list[Edge], tree: set[int]) -> int:
    components = component_data(n, primal, tree)
    return sum(len(vertices) - 2 * beta for vertices, _, beta in components)


def exchange_cycle(
    dual: list[tuple[Face, Face]], tree: set[int], added: int
) -> list[int]:
    adjacency: dict[Face, list[tuple[Face, int]]] = defaultdict(list)
    for index in tree:
        left, right = dual[index]
        adjacency[left].append((right, index))
        adjacency[right].append((left, index))
    source, target = dual[added]
    queue = deque([source])
    parent: dict[Face, tuple[Face, int] | None] = {source: None}
    while target not in parent:
        face = queue.popleft()
        for neighbor, index in adjacency[face]:
            if neighbor not in parent:
                parent[neighbor] = (face, index)
                queue.append(neighbor)
    cycle: list[int] = []
    face = target
    while parent[face] is not None:
        face, index = parent[face]
        cycle.append(index)
    return cycle


def search(
    n: int, restarts: int, steps: int, seed: int, initial: set[int] | None = None
) -> tuple[set[int], int]:
    rng = random.Random(seed)
    primal, dual = grid_and_dual_edges(n)
    best_tree: set[int] | None = None
    best = 10**9
    for restart in range(restarts):
        tree = set(initial) if restart == 0 and initial is not None else random_dual_tree(n, dual, rng)
        value = curvature(n, primal, tree)
        for step in range(steps):
            added = rng.choice([index for index in range(len(dual)) if index not in tree])
            removed = rng.choice(exchange_cycle(dual, tree, added))
            candidate = tree - {removed} | {added}
            candidate_value = curvature(n, primal, candidate)
            temperature = max(0.05, 2.0 * (1.0 - step / steps))
            accept = candidate_value <= value or rng.random() < pow(2.718281828, (value - candidate_value) / temperature)
            if accept:
                tree, value = candidate, candidate_value
            if value < best:
                best_tree, best = set(tree), value
        if best < n:
            break
    assert best_tree is not None
    return best_tree, best


def witness_complement(n: int, primal: list[Edge]) -> set[int]:
    output = subprocess.run(
        ["target/release/grid_graphs", "witness", str(n), str(n)],
        check=True,
        capture_output=True,
        text=True,
    ).stdout
    chosen = {
        tuple(sorted((int(r1) * n + int(c1), int(r2) * n + int(c2))))
        for line in output.splitlines()
        if line and not line.startswith("#")
        for r1, c1, r2, c2 in [line.split()]
    }
    return {index for index, edge in enumerate(primal) if tuple(sorted(edge)) not in chosen}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("n", type=int)
    parser.add_argument("--restarts", type=int, default=100)
    parser.add_argument("--steps", type=int, default=2000)
    parser.add_argument("--seed", type=int, default=1)
    parser.add_argument("--from-witness", action="store_true")
    parser.add_argument("--start-witness", action="store_true")
    args = parser.parse_args()
    primal, _ = grid_and_dual_edges(args.n)
    if args.from_witness:
        tree = witness_complement(args.n, primal)
        value = curvature(args.n, primal, tree)
    else:
        initial = witness_complement(args.n, primal) if args.start_witness else None
        tree, value = search(args.n, args.restarts, args.steps, args.seed, initial)
    components = component_data(args.n, primal, tree)
    waste = 3 * len({vertex for index in tree for vertex in primal[index]}) - 2 * len(tree)
    print(f"n={args.n} P={value} W={waste} components={len(components)}")
    for vertices, edges, beta in components:
        coordinates = [(vertex // args.n, vertex % args.n) for vertex in vertices]
        print(f"component vertices={coordinates} edges={edges} beta={beta} term={len(vertices) - 2 * beta}")
    print("D edges:")
    for index in sorted(tree):
        left, right = primal[index]
        print(left // args.n, left % args.n, right // args.n, right % args.n)


if __name__ == "__main__":
    main()
