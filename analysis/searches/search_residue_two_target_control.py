#!/usr/bin/env python3
"""Exact low-order net-cost controls around a connected construction.

For a source pattern at cost C, order ``a`` adds ``a`` non-U vertices and
removes ``a + deficit`` source U vertices.  Removal tuples are drawn only from
vertices individually removable after the additions.  This is exact:
connectivity after deleting a set implies connectivity after deleting each
member separately, since restoring edges cannot destroy connectivity.

Individual removability is evaluated without rerunning a graph traversal.  For
each source U, the components left after deleting its incident dual edges are
precomputed once.  An augmentation makes that U removable exactly when its few
new dual edges reconnect those fixed components.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from collections import Counter
from dataclasses import dataclass
from math import comb
from pathlib import Path

from analysis._paths import ANALYSIS_ROOT
from analysis.patterns.construction_lab import (
    dual_connectivity_check,
    forest_completion_check,
    run_check,
)

HERE = ANALYSIS_ROOT
DEFAULT_INPUT = HERE / "residue_two_b20_to_b23_basic_result.json"
DEFAULT_OUTPUT = HERE / "residue_two_n23_target_control_result.json"
SCHEMA = "grid-graphs.residue-two-target-control.v3"


Cell = tuple[int, int]


@dataclass(frozen=True, slots=True)
class DualEdge:
    cells: tuple[Cell, Cell]
    faces: tuple[int, int]


@dataclass(frozen=True, slots=True)
class RemovalProfile:
    labels: tuple[int, ...]
    component_count: int


def grid_dual_edges(n: int) -> tuple[DualEdge, ...]:
    def face(row: int, column: int) -> int:
        return 1 + row * (n - 1) + column

    edges = []
    for row in range(n):
        for column in range(n - 1):
            faces = (
                0 if row == 0 else face(row - 1, column),
                0 if row == n - 1 else face(row, column),
            )
            edges.append(DualEdge(((row, column), (row, column + 1)), faces))
    for row in range(n - 1):
        for column in range(n):
            faces = (
                0 if column == 0 else face(row, column - 1),
                0 if column == n - 1 else face(row, column),
            )
            edges.append(DualEdge(((row, column), (row + 1, column)), faces))
    return tuple(edges)


class ConnectivitySensitivity:
    """Exact source-edge deletion profiles for cheap augmentation queries."""

    def __init__(self, rows: list[str]):
        self.n = len(rows)
        self.source_u = tuple(
            (row, column)
            for row, values in enumerate(rows)
            for column, value in enumerate(values)
            if value == "U"
        )
        self.source_u_set = frozenset(self.source_u)
        self.edges = grid_dual_edges(self.n)
        self.edge_by_cells = {frozenset(edge.cells): edge for edge in self.edges}
        self.face_count = 1 + (self.n - 1) ** 2
        self.source_edges = tuple(
            edge
            for edge in self.edges
            if edge.cells[0] in self.source_u_set and edge.cells[1] in self.source_u_set
        )
        self.profiles = {
            cell: self._profile_without(cell) for cell in self.source_u
        }
        self._pair_bits = []
        self._connected = []
        for cell in self.source_u:
            profile = self.profiles[cell]
            pairs = {
                pair: 1 << index
                for index, pair in enumerate(
                    itertools.combinations(range(profile.component_count), 2)
                )
            }
            self._pair_bits.append(pairs)
            connected = []
            for mask in range(1 << len(pairs)):
                parent = list(range(profile.component_count))

                def find(value: int) -> int:
                    while parent[value] != value:
                        parent[value] = parent[parent[value]]
                        value = parent[value]
                    return value

                for (left, right), bit in pairs.items():
                    if mask & bit:
                        left_root, right_root = find(left), find(right)
                        if left_root != right_root:
                            parent[right_root] = left_root
                connected.append(
                    len({find(component) for component in range(profile.component_count)}) == 1
                )
            self._connected.append(tuple(connected))
        self.source_dots = tuple(
            (row, column)
            for row in range(self.n)
            for column in range(self.n)
            if (row, column) not in self.source_u_set
        )
        self._addition_masks = {
            addition: self._masks_for_edges(self.new_edges((addition,)))
            for addition in self.source_dots
        }
        self._dot_index = {cell: index for index, cell in enumerate(self.source_dots)}
        suffix = [None] * (len(self.source_dots) + 1)
        suffix[-1] = (0,) * len(self.source_u)
        for index in range(len(self.source_dots) - 1, -1, -1):
            suffix[index] = tuple(
                left | right
                for left, right in zip(
                    self._addition_masks[self.source_dots[index]],
                    suffix[index + 1],
                    strict=True,
                )
            )
        self._addition_suffix_masks = tuple(suffix)

    def _profile_without(self, removed: Cell) -> RemovalProfile:
        adjacency = [[] for _ in range(self.face_count)]
        for edge in self.source_edges:
            if removed in edge.cells or edge.faces[0] == edge.faces[1]:
                continue
            left, right = edge.faces
            adjacency[left].append(right)
            adjacency[right].append(left)
        labels = [-1] * self.face_count
        component_count = 0
        for start in range(self.face_count):
            if labels[start] >= 0:
                continue
            labels[start] = component_count
            stack = [start]
            while stack:
                vertex = stack.pop()
                for neighbor in adjacency[vertex]:
                    if labels[neighbor] < 0:
                        labels[neighbor] = component_count
                        stack.append(neighbor)
            component_count += 1
        return RemovalProfile(tuple(labels), component_count)

    def new_edges(self, additions: tuple[Cell, ...]) -> tuple[DualEdge, ...]:
        active = self.source_u_set | frozenset(additions)
        return tuple(
            edge
            for edge in self.edges
            if edge not in self.source_edges
            and edge.cells[0] in active
            and edge.cells[1] in active
        )

    def _masks_for_edges(self, edges: tuple[DualEdge, ...]) -> tuple[int, ...]:
        masks = []
        for index, cell in enumerate(self.source_u):
            profile = self.profiles[cell]
            mask = 0
            for edge in edges:
                if cell in edge.cells:
                    continue
                left, right = sorted(
                    (profile.labels[edge.faces[0]], profile.labels[edge.faces[1]])
                )
                if left != right:
                    mask |= self._pair_bits[index][(left, right)]
            masks.append(mask)
        return tuple(masks)

    def combined_masks(self, additions: tuple[Cell, ...]) -> tuple[int, ...]:
        masks = [0] * len(self.source_u)
        for addition in additions:
            contribution = self._addition_masks[addition]
            for index, mask in enumerate(contribution):
                masks[index] |= mask
        for pair in itertools.combinations(additions, 2):
            edge = self.edge_by_cells.get(frozenset(pair))
            if edge is None:
                continue
            contribution = self._masks_for_edges((edge,))
            for index, mask in enumerate(contribution):
                masks[index] |= mask
        return tuple(masks)

    def individually_removable(
        self,
        additions: tuple[Cell, ...],
        possible_indices: tuple[int, ...] | None = None,
    ) -> tuple[Cell, ...]:
        masks = self.combined_masks(additions)
        indices = range(len(self.source_u)) if possible_indices is None else possible_indices
        return tuple(
            self.source_u[index]
            for index in indices
            if self._connected[index][masks[index]]
        )

    def optimistic_third_indices(
        self, pair: tuple[Cell, Cell], allowed_thirds: tuple[Cell, ...]
    ) -> tuple[int, ...]:
        """Exact superset of removable U indices for every allowed pair extension."""
        masks = list(self.combined_masks(pair))
        if not allowed_thirds:
            return ()
        first = self._dot_index[allowed_thirds[0]]
        for index, mask in enumerate(self._addition_suffix_masks[first]):
            masks[index] |= mask
        allowed = frozenset(allowed_thirds)
        for endpoint in pair:
            row, column = endpoint
            for delta_row, delta_column in ((-1, 0), (1, 0), (0, -1), (0, 1)):
                third = row + delta_row, column + delta_column
                if third not in allowed:
                    continue
                edge = self.edge_by_cells[frozenset((endpoint, third))]
                contribution = self._masks_for_edges((edge,))
                for index, mask in enumerate(contribution):
                    masks[index] |= mask
        return tuple(
            index
            for index, mask in enumerate(masks)
            if self._connected[index][mask]
        )


def rows_sha256(rows: list[str]) -> str:
    return hashlib.sha256(("\n".join(rows) + "\n").encode("ascii")).hexdigest()


def changed_rows(
    rows: list[str], additions: tuple[tuple[int, int], ...], removals: tuple[tuple[int, int], ...]
) -> list[str]:
    result = [list(row) for row in rows]
    for row, column in additions:
        if result[row][column] != ".":
            raise ValueError("addition is not a dot in the source pattern")
        result[row][column] = "U"
    for row, column in removals:
        if result[row][column] != "U":
            raise ValueError("removal is not U after additions")
        result[row][column] = "."
    return ["".join(row) for row in result]


def search(
    rows: list[str],
    deficit: int = 2,
    maximum_additions: int = 3,
    *,
    shard_count: int = 1,
    shard_index: int = 0,
) -> dict:
    n = len(rows)
    if any(len(row) != n for row in rows):
        raise ValueError("source pattern must be square")
    source_u = tuple(
        (row, column)
        for row, values in enumerate(rows)
        for column, value in enumerate(values)
        if value == "U"
    )
    source_dots = tuple(
        (row, column)
        for row, values in enumerate(rows)
        for column, value in enumerate(values)
        if value == "."
    )
    source_dual = dual_connectivity_check(rows)
    source_forest = forest_completion_check(rows)
    if not source_dual[0] or not source_forest[0]:
        raise ValueError("source must be connected and forest-completable")
    if deficit < 1 or maximum_additions not in (0, 1, 2, 3):
        raise ValueError("this implementation supports positive deficits and orders zero through three")
    if shard_count < 1 or not 0 <= shard_index < shard_count:
        raise ValueError("shard index must lie in [0, shard_count)")

    sensitivity = ConnectivitySensitivity(rows)

    orders = []
    witnesses = []
    for addition_count in range(maximum_additions + 1):
        removal_count = addition_count + deficit
        tested = connected = forest = 0
        candidate_histogram: Counter[int] = Counter()
        qualifying_controls = []
        qualifying_samples = []
        dual_connected_survivors = []
        qualifying_count = prefilter_pruned = assigned = 0
        qualifying_digest = hashlib.sha256()

        def process(additions: tuple[Cell, ...], candidates: tuple[Cell, ...]) -> None:
            nonlocal tested, connected, forest, qualifying_count
            augmented = changed_rows(rows, additions, ())
            if addition_count:
                candidate_histogram[len(candidates)] += 1
                if len(candidates) >= removal_count:
                    control = {"additions": additions, "individually_removable": candidates}
                    qualifying_count += 1
                    qualifying_digest.update(
                        (json.dumps(control, separators=(",", ":")) + "\n").encode("ascii")
                    )
                    if addition_count < 3:
                        qualifying_controls.append(control)
                    elif len(qualifying_samples) < 8:
                        qualifying_samples.append(control)
            for removals in itertools.combinations(candidates, removal_count):
                tested += 1
                candidate = changed_rows(augmented, (), removals)
                if not dual_connectivity_check(candidate)[0]:
                    continue
                connected += 1
                forest_ok, forest_reason = forest_completion_check(candidate)
                dual_connected_survivors.append(
                    {
                        "additions": additions,
                        "removals": removals,
                        "sha256": rows_sha256(candidate),
                        "forest_ok": forest_ok,
                        "forest_reason": forest_reason,
                        "rows": candidate,
                    }
                )
                if not forest_ok:
                    continue
                forest += 1
                validation = run_check(
                    n, candidate, expected_u=len(source_u) - deficit, verbose=False
                )
                if not validation["all_ok"]:
                    raise AssertionError("control witness failed construction_lab replay")
                witnesses.append(
                    {
                        "addition_count": addition_count,
                        "additions": additions,
                        "removals": removals,
                        "sha256": rows_sha256(candidate),
                        "rows": candidate,
                        "validation": validation,
                    }
                )

        if addition_count < 3:
            for ordinal, additions in enumerate(
                itertools.combinations(source_dots, addition_count)
            ):
                if ordinal % shard_count != shard_index:
                    continue
                assigned += 1
                candidates = (
                    source_u
                    if addition_count == 0
                    else sensitivity.individually_removable(additions)
                )
                process(additions, candidates)
        else:
            ordinal = 0
            for left in range(len(source_dots) - 2):
                for middle in range(left + 1, len(source_dots) - 1):
                    thirds = source_dots[middle + 1 :]
                    possible = sensitivity.optimistic_third_indices(
                        (source_dots[left], source_dots[middle]), thirds
                    )
                    for third in thirds:
                        in_shard = ordinal % shard_count == shard_index
                        ordinal += 1
                        if not in_shard:
                            continue
                        assigned += 1
                        if len(possible) < removal_count:
                            prefilter_pruned += 1
                            continue
                        additions = source_dots[left], source_dots[middle], third
                        candidates = sensitivity.individually_removable(additions, possible)
                        process(additions, candidates)
        orders.append(
            {
                "addition_count": addition_count,
                "removal_count": removal_count,
                "addition_sets": comb(len(source_dots), addition_count),
                "addition_sets_assigned_to_shard": assigned,
                "pair_optimistic_prefilter_pruned": prefilter_pruned,
                "candidate_removal_tuples_tested": tested,
                "dual_connected": connected,
                "forest_completable": forest,
                "individual_candidate_count_histogram": (
                    None
                    if addition_count == 0
                    else {str(key): candidate_histogram[key] for key in sorted(candidate_histogram)}
                ),
                "individual_candidate_histogram_scope": (
                    None
                    if addition_count == 0
                    else "assigned addition sets not eliminated by the exact pair-optimistic prefilter"
                ),
                "prefilter_guarantee": (
                    None
                    if addition_count < 3
                    else "every pruned triple has fewer than five individually removable source U cells"
                ),
                "qualifying_addition_sets": qualifying_count,
                "qualifying_controls_sha256": qualifying_digest.hexdigest(),
                "qualifying_individual_controls": qualifying_controls,
                "qualifying_individual_control_samples": qualifying_samples,
                "dual_connected_survivors": dual_connected_survivors,
            }
        )

    return {
        "schema": SCHEMA,
        "status": (
            "SAT"
            if witnesses
            else "UNSAT_IN_DECLARED_NEIGHBORHOOD"
            if shard_count == 1
            else "UNSAT_IN_DECLARED_SHARD"
        ),
        "exact_in_declared_neighborhood": shard_count == 1,
        "scope": {
            "n": n,
            "source_u": len(source_u),
            "target_u": len(source_u) - deficit,
            "net_cost_deficit": deficit,
            "maximum_additions": maximum_additions,
            "orders": "for each a=0..maximum_additions, add a dots and remove a+deficit source U cells",
            "addition_domain": "every dot of the source pattern",
            "removal_domain": "every U of the source pattern; added cells are not removable",
            "outside_changes": "none",
            "sharding": {
                "shard_count": shard_count,
                "shard_index": shard_index,
                "partition": "zero-based lexicographic addition-set ordinal modulo shard_count",
            },
            "negative_scope_note": (
                "A negative result excludes only these bounded exchanges around this one "
                "source witness; it is not a global n=23 impossibility result."
            ),
        },
        "source": {
            "sha256": rows_sha256(rows),
            "dual_connected": source_dual[1],
            "dual_total": source_dual[2],
            "forest_ok": source_forest[0],
            "forest_reason": source_forest[1],
        },
        "method": {
            "candidate_connectivity": (
                "precomputed exact components of the source dual after each bundled "
                "source-U edge deletion, reconnected by augmentation edges"
            ),
            "candidate_replay_connectivity": "construction_lab.dual_connectivity_check",
            "forest_completion": "construction_lab.forest_completion_check",
            "monotonic_reduction": (
                "If G-S is connected, then G-{v} is connected for every v in S; "
                "therefore only individually removable source U cells can occur in a valid tuple."
            ),
            "source_removal_component_histogram": {
                str(key): value
                for key, value in sorted(
                    Counter(
                        profile.component_count for profile in sensitivity.profiles.values()
                    ).items()
                )
            },
        },
        "orders": orders,
        "witnesses": witnesses,
    }


def load_source(path: Path) -> list[str]:
    record = json.loads(path.read_text())
    try:
        return record["budgets"]["335"]["witness"]
    except (KeyError, TypeError) as error:
        raise ValueError("input must contain budgets.335.witness") from error


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--deficit", type=int, default=2)
    parser.add_argument("--maximum-additions", type=int, choices=(0, 1, 2, 3), default=3)
    parser.add_argument("--shard-count", type=int, default=1)
    parser.add_argument("--shard-index", type=int, default=0)
    args = parser.parse_args()
    record = search(
        load_source(args.input),
        args.deficit,
        args.maximum_additions,
        shard_count=args.shard_count,
        shard_index=args.shard_index,
    )
    args.output.write_text(json.dumps(record, indent=2) + "\n")
    print(
        f"wrote {args.output}: {record['status']}; "
        f"tested={[order['candidate_removal_tuples_tested'] for order in record['orders']]}"
    )


if __name__ == "__main__":
    main()
