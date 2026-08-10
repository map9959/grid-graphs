#!/usr/bin/env python3
"""Exact row grammar for computational discovery of forced forests.

For a binary vertex set F, the forced graph contains exactly the grid edges
with at least one endpoint in F.  This module maximizes |F| subject to that
graph being a forest.  It is a finite exact computation, intended for proof
discovery and checking small instances; it is not a theorem or a proof of a
formula for uncomputed sizes.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from typing import Iterable


Partition = tuple[int, ...]


@dataclass(frozen=True)
class State:
    """Processed-prefix state at the active (most recently added) row.

    ``forced_mask`` records F on that row. ``partition[c]`` is the canonical
    component label of its vertex in the processed forced graph. Components
    not meeting this row have retired and are deliberately absent.
    """

    forced_mask: int
    partition: Partition


class _DisjointSet:
    def __init__(self, size: int) -> None:
        self.parent = list(range(size))
        self.rank = [0] * size

    def find(self, vertex: int) -> int:
        while self.parent[vertex] != vertex:
            self.parent[vertex] = self.parent[self.parent[vertex]]
            vertex = self.parent[vertex]
        return vertex

    def union_edge(self, left: int, right: int) -> bool:
        """Insert an edge, returning false exactly when it closes a cycle."""
        left_root = self.find(left)
        right_root = self.find(right)
        if left_root == right_root:
            return False
        if self.rank[left_root] < self.rank[right_root]:
            left_root, right_root = right_root, left_root
        self.parent[right_root] = left_root
        if self.rank[left_root] == self.rank[right_root]:
            self.rank[left_root] += 1
        return True

    def union_summary(self, left: int, right: int) -> None:
        """Restore already-known connectivity without inserting a new edge."""
        left_root = self.find(left)
        right_root = self.find(right)
        if left_root != right_root:
            self.parent[right_root] = left_root


def _canonical_partition(dsu: _DisjointSet, vertices: Iterable[int]) -> Partition:
    labels: dict[int, int] = {}
    result = []
    for vertex in vertices:
        root = dsu.find(vertex)
        if root not in labels:
            labels[root] = len(labels)
        result.append(labels[root])
    return tuple(result)


def first_row_state(width: int, forced_mask: int) -> State | None:
    """Build the state for a first row, or reject its forced-edge cycle."""
    _validate_mask(width, forced_mask)
    dsu = _DisjointSet(width)
    for column in range(width - 1):
        if forced_mask & (3 << column):
            if not dsu.union_edge(column, column + 1):
                return None
    return State(forced_mask, _canonical_partition(dsu, range(width)))


def transition(width: int, state: State, forced_mask: int) -> State | None:
    """Append one row and return its state, rejecting forced-edge cycles.

    Previous-row vertices are 0..width-1 and new-row vertices are
    width..2*width-1. The old partition restores paths in the processed prefix;
    all forced vertical and new horizontal edges are then inserted exactly once.
    """
    _validate_mask(width, forced_mask)
    if len(state.partition) != width:
        raise ValueError("state partition width does not match width")

    dsu = _DisjointSet(2 * width)
    representatives: dict[int, int] = {}
    for column, label in enumerate(state.partition):
        if label in representatives:
            dsu.union_summary(representatives[label], column)
        else:
            representatives[label] = column

    for column in range(width):
        if (state.forced_mask | forced_mask) & (1 << column):
            if not dsu.union_edge(column, width + column):
                return None
    for column in range(width - 1):
        if forced_mask & (3 << column):
            if not dsu.union_edge(width + column, width + column + 1):
                return None

    partition = _canonical_partition(dsu, range(width, 2 * width))
    return State(forced_mask, partition)


def maximum_forced_forest(n: int, *, witness: bool = False) -> int | tuple[int, list[int]]:
    """Return the exact maximum |F| on the n by n grid.

    With ``witness=True``, also return the maximizing row masks, top to bottom.
    The dynamic program merges equal frontier states while retaining maximum
    cost. This computes a finite instance only and makes no theorem claim.
    """
    if n <= 0:
        raise ValueError("n must be positive")

    costs: dict[State, int] = {}
    parents: list[dict[State, State | None]] = []
    first_parents: dict[State, State | None] = {}
    for mask in range(1 << n):
        state = first_row_state(n, mask)
        if state is not None:
            costs[state] = mask.bit_count()
            if witness:
                first_parents[state] = None
    if witness:
        parents.append(first_parents)

    for _row in range(1, n):
        next_costs: dict[State, int] = {}
        next_parents: dict[State, State | None] = {}
        for state, cost in costs.items():
            for mask in range(1 << n):
                next_state = transition(n, state, mask)
                if next_state is None:
                    continue
                next_cost = cost + mask.bit_count()
                if next_cost > next_costs.get(next_state, -1):
                    next_costs[next_state] = next_cost
                    if witness:
                        next_parents[next_state] = state
        costs = next_costs
        if witness:
            parents.append(next_parents)

    final_state = max(costs, key=costs.__getitem__)
    maximum = costs[final_state]
    if not witness:
        return maximum

    masks = [0] * n
    state: State | None = final_state
    for row in range(n - 1, -1, -1):
        assert state is not None
        masks[row] = state.forced_mask
        state = parents[row][state]
    return maximum, masks


def is_forced_forest(n: int, row_masks: list[int]) -> bool:
    """Directly check a square row-mask candidate, independently of the DP."""
    if n <= 0 or len(row_masks) != n:
        return False
    if any(mask < 0 or mask >= 1 << n for mask in row_masks):
        return False
    dsu = _DisjointSet(n * n)
    for row in range(n):
        for column in range(n):
            vertex = row * n + column
            if column + 1 < n and row_masks[row] & (3 << column):
                if not dsu.union_edge(vertex, vertex + 1):
                    return False
            if row + 1 < n and (row_masks[row] | row_masks[row + 1]) & (1 << column):
                if not dsu.union_edge(vertex, vertex + n):
                    return False
    return True


def _validate_mask(width: int, forced_mask: int) -> None:
    if width <= 0:
        raise ValueError("width must be positive")
    if forced_mask < 0 or forced_mask >= 1 << width:
        raise ValueError("forced mask does not fit width")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("n", type=int, help="square side length")
    parser.add_argument("--witness", action="store_true", help="print maximizing F rows")
    args = parser.parse_args()
    result = maximum_forced_forest(args.n, witness=args.witness)
    if not args.witness:
        print(result)
        return
    maximum, masks = result
    print(f"# finite exact computation only: n={args.n} max_forced={maximum}")
    for mask in masks:
        print("".join("F" if mask & (1 << column) else "." for column in range(args.n)))


if __name__ == "__main__":
    main()
