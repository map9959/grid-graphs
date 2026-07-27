#!/usr/bin/env python3
"""Exact trims of the connected 179-U affine n=17 residue-two candidate."""

from __future__ import annotations

import argparse
from itertools import combinations
from pathlib import Path

from construction_lab import run_check
from diagonal_patterns import residue_two_affine_pattern
from search_residue_anneal import bits_to_rows, dual_metrics, rows_to_bits


AFFINE_179 = residue_two_affine_pattern(17)

AFFINE_178 = [
    ".U...............",
    ".UUUUUUUUUUUUUUUU",
    ".UUUU.UU.UU.UU.UU",
    ".UU.UUUU.UU.UUUU.",
    ".UU.UU.U.UUUU.UU.",
    ".UU.UU.UUU.UU.UU.",
    ".UU.UU.UUU.UU.UU.",
    ".UU.UU.U.U.UU.UU.",
    ".UU.UU.UUU.UU.UU.",
    ".UU.UU.UUU.UU.UU.",
    ".UU.UUUU.U.UU.UU.",
    ".UU.U.UUUU.UU.UU.",
    ".UUUU.U.UU.UU.UU.",
    ".U.UUUU.UU.UU.UU.",
    ".UUU.UU.UU.UU.UU.",
    ".UUUUUUUUUUUUUUU.",
    ".U.............U.",
]


def active_dual_edges(bits: int, n: int):
    side = n - 1

    def face(row: int, column: int) -> int:
        return 1 + row * side + column

    edges = []
    for row in range(n):
        for column in range(side):
            left = row * n + column
            right = left + 1
            if bits & (1 << left) and bits & (1 << right):
                edges.append(
                    (
                        left,
                        right,
                        0 if row == 0 else face(row - 1, column),
                        0 if row + 1 == n else face(row, column),
                    )
                )
    for row in range(side):
        for column in range(n):
            top = row * n + column
            bottom = top + n
            if bits & (1 << top) and bits & (1 << bottom):
                edges.append(
                    (
                        top,
                        bottom,
                        0 if column == 0 else face(row, column - 1),
                        0 if column + 1 == n else face(row, column),
                    )
                )
    return edges


def bridge_edges(edges, total_faces: int) -> set[int]:
    adjacency = [[] for _ in range(total_faces)]
    for edge_id, (_, _, left, right) in enumerate(edges):
        adjacency[left].append((right, edge_id))
        adjacency[right].append((left, edge_id))
    discovery = [-1] * total_faces
    low = [0] * total_faces
    bridges = set()
    clock = 0

    def visit(vertex: int, parent_edge: int) -> None:
        nonlocal clock
        discovery[vertex] = low[vertex] = clock
        clock += 1
        for neighbor, edge_id in adjacency[vertex]:
            if edge_id == parent_edge:
                continue
            if discovery[neighbor] < 0:
                visit(neighbor, edge_id)
                low[vertex] = min(low[vertex], low[neighbor])
                if low[neighbor] > discovery[vertex]:
                    bridges.add(edge_id)
            else:
                low[vertex] = min(low[vertex], discovery[neighbor])

    visit(0, -1)
    if any(value < 0 for value in discovery):
        raise AssertionError("augmented affine dual unexpectedly disconnected")
    return bridges


def search(
    n: int, add_row_start: int, add_row_end: int, add_count: int, source: str = "affine"
) -> bool:
    if source == "middle250":
        if n != 20:
            raise ValueError("middle250 source requires n=20")
        from search_residue_two_middle import KNOWN_250

        source_rows = KNOWN_250
    elif source == "phase250":
        if n != 20:
            raise ValueError("phase250 source requires n=20")
        source_rows = Path(__file__).with_name(
            "residue_two_phase_front_witness.txt"
        ).read_text().splitlines()
    else:
        source_rows = residue_two_affine_pattern(n)
    bits = rows_to_bits(source_rows)
    baseline = dual_metrics(bits, n)
    if baseline.components != 1:
        raise AssertionError(f"{source} candidate regression")
    original_us = [vertex for vertex in range(n * n) if bits & (1 << vertex)]
    dots = [
        vertex
        for vertex in range(n * n)
        if not bits & (1 << vertex)
    ]
    additions = (
        added
        for added in combinations(dots, add_count)
        if add_row_start <= min(vertex // n for vertex in added) < add_row_end
    )
    addition_count = 0
    checked = 0
    bridge_pruned = 0
    edge_pruned = 0
    for added in additions:
        addition_count += 1
        augmented = bits
        for vertex in added:
            augmented |= 1 << vertex
        edges = active_dual_edges(augmented, n)
        bridges = bridge_edges(edges, (n - 1) ** 2 + 1)
        bundles = {vertex: set() for vertex in original_us}
        for edge_id, (first, second, _, _) in enumerate(edges):
            if first in bundles:
                bundles[first].add(edge_id)
            if second in bundles:
                bundles[second].add(edge_id)
        eligible = [
            vertex
            for vertex in original_us
            if bundles[vertex].isdisjoint(bridges)
        ]
        bridge_pruned += len(original_us) - len(eligible)
        cycle_budget = len(edges) - ((n - 1) ** 2 + 1) + 1
        for removed in combinations(eligible, add_count + 1):
            deleted_edges = set().union(*(bundles[vertex] for vertex in removed))
            if len(deleted_edges) > cycle_budget:
                edge_pruned += 1
                continue
            checked += 1
            candidate = augmented
            for vertex in removed:
                candidate &= ~(1 << vertex)
            metrics = dual_metrics(candidate, n)
            if metrics.components != 1:
                continue
            rows = bits_to_rows(candidate, n)
            info = run_check(n, rows, verbose=True)
            if not info["all_ok"]:
                raise AssertionError(f"connected {source} trim failed verification")
            print(
                f"found add={[divmod(v, n) for v in added]} "
                f"remove={[divmod(v, n) for v in removed]}"
            )
            print("\n".join(rows))
            return True
    print(
        f"no {add_count}-add/{add_count + 1}-remove trim from {source} "
        f"rows={add_row_start}..{add_row_end - 1}; "
        f"additions={addition_count} exact_checks={checked} "
        f"bridge_pruned_vertices={bridge_pruned} edge_pruned_pairs={edge_pruned}"
    )
    return False


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, default=17)
    parser.add_argument("--add-row-start", type=int, default=0)
    parser.add_argument("--add-row-end", type=int)
    parser.add_argument("--add-count", type=int, choices=(1, 2, 3, 4), default=1)
    parser.add_argument(
        "--source", choices=("affine", "middle250", "phase250"), default="affine"
    )
    args = parser.parse_args()
    add_row_end = args.n if args.add_row_end is None else args.add_row_end
    if not 0 <= args.add_row_start < add_row_end <= args.n:
        raise ValueError(f"addition row range must lie in 0..{args.n}")
    if not search(args.n, args.add_row_start, add_row_end, args.add_count, args.source):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
