#!/usr/bin/env python3
"""Exhaust the bounded L3 grammar for the residue-two counter surgery."""

from __future__ import annotations

import argparse
import json
from collections import Counter
from functools import lru_cache
from itertools import combinations
from pathlib import Path

from analysis.patterns.construction_lab import forest_completion_check
from analysis.patterns.diagonal_patterns import residue_two_affine_pattern
from analysis.residue_geometry.check_residue_two_affine_interval_skeleton import (
    _components,
    _forced_star,
    _interval_id,
    _is_acyclic,
    _is_straight_interval,
)

Vertex = tuple[int, int]
SCHEMA = "grid-graphs.residue-two-counter-interval-geometry-census.v1"
WINDOW_SIDE = 7
MAX_DELETE = 3
COUNTER_LABEL = "C:counter"


def _preserved(k: int) -> set[Vertex]:
    n = 3 * k + 2
    return {
        (row, column)
        for row, values in enumerate(residue_two_affine_pattern(n))
        for column, value in enumerate(values)
        if value == "."
    }


def _rows(vertices: set[Vertex], n: int) -> list[str]:
    return [
        "".join("." if (row, column) in vertices else "U" for column in range(n))
        for row in range(n)
    ]


def _local_cell_violation(
    vertices: set[Vertex], changed: set[Vertex], n: int
) -> dict | None:
    cells = {
        (row, column)
        for r, c in changed
        for row in (r - 1, r)
        for column in (c - 1, c)
        if 0 <= row < n - 1 and 0 <= column < n - 1
    }
    for row, column in cells:
        present = {
            (dr, dc)
            for dr in (0, 1)
            for dc in (0, 1)
            if (row + dr, column + dc) in vertices
        }
        if len(present) >= 3:
            return {
                "cell": [row, column],
                "type": "three_or_four_preserved_vertices",
                "preserved_offsets": [list(offset) for offset in sorted(present)],
            }
        if len(present) == 2 and (
            {(0, 0), (1, 1)} <= present or {(0, 1), (1, 0)} <= present
        ):
            return {
                "cell": [row, column],
                "type": "preserved_diagonal_pair",
                "preserved_offsets": [list(offset) for offset in sorted(present)],
            }
    return None


def _local_cell_condition(vertices: set[Vertex], changed: set[Vertex], n: int) -> bool:
    return _local_cell_violation(vertices, changed, n) is None


def _classify(
    k: int,
    base: set[Vertex],
    base_components: list[frozenset[Vertex]],
    base_edges: set[frozenset[str]],
    counter: frozenset[Vertex],
    deleted: frozenset[Vertex],
    added: frozenset[Vertex],
) -> tuple[str, dict]:
    n = 3 * k + 2
    vertices = (base - deleted) | set(counter) | set(added)
    changed = set(counter) | set(deleted) | set(added)
    if len(vertices) != 3 * k * k + 7 * k:
        return "wrong_count", {}
    violation = _local_cell_violation(vertices, changed, n)
    if violation is not None:
        return "forbidden_unit_cell", violation

    components = _components(vertices, n)
    if not all(_is_straight_interval(component) for component in components):
        return "nonstraight_component", {}
    if counter not in components:
        return "counter_not_exact_component", {}
    if len(components) != len(base_components) + 1:
        return "wrong_component_count", {"observed": len(components)}

    labels: dict[frozenset[Vertex], str] = {counter: COUNTER_LABEL}
    used = set()
    for component in components:
        if component == counter:
            continue
        overlaps = [
            index for index, old in enumerate(base_components) if component & old
        ]
        if len(overlaps) != 1 or overlaps[0] in used:
            return "noninjective_component_transport", {"overlaps": overlaps}
        index = overlaps[0]
        used.add(index)
        labels[component] = _interval_id(base_components[index])
    if len(used) != len(base_components):
        return "missing_old_component", {"mapped": len(used)}

    stars = {component: _forced_star(component, n) for component in components}
    if not all(_is_acyclic(edges) for edges, _ in stars.values()):
        return "cyclic_interval_star", {}
    observed_edges = set()
    attachments = {}
    for left_index, left in enumerate(components):
        for right in components[left_index + 1:]:
            intersection = stars[left][1] & stars[right][1]
            if len(intersection) > 1:
                return "multiple_star_intersection", {
                    "left": labels[left],
                    "right": labels[right],
                    "size": len(intersection),
                }
            if intersection:
                edge = frozenset((labels[left], labels[right]))
                observed_edges.add(edge)
                attachments["|".join(sorted(edge))] = list(next(iter(intersection)))

    root = f"H:r0:c2..{3 * k + 1}"
    branch = f"V:c0:r0..{3 * k + 1}"
    expected_edges = base_edges - {frozenset((root, branch))}
    expected_edges |= {
        frozenset((root, COUNTER_LABEL)),
        frozenset((COUNTER_LABEL, branch)),
    }
    if observed_edges != expected_edges:
        return "undeclared_incidence", {
            "missing": [sorted(edge) for edge in sorted(expected_edges - observed_edges, key=sorted)],
            "extra": [sorted(edge) for edge in sorted(observed_edges - expected_edges, key=sorted)],
        }

    forest_ok, reason = forest_completion_check(_rows(vertices, n))
    if not forest_ok:
        return "forced_graph_not_forest", {"reason": reason}
    return "realization", {
        "attachments": attachments,
        "preserved_count": len(vertices),
    }


def _base_incidence(
    components: list[frozenset[Vertex]], n: int
) -> set[frozenset[str]]:
    supports = [_forced_star(component, n)[1] for component in components]
    return {
        frozenset((_interval_id(components[left]), _interval_id(components[right])))
        for left in range(len(components))
        for right in range(left + 1, len(components))
        if supports[left] & supports[right]
    }


def replay_choice(k: int, replay: dict) -> tuple[str, dict]:
    """Replay one serialized `(counter, deleted, added)` census choice."""
    n = 3 * k + 2
    base = _preserved(k)
    components = _components(base, n)
    return _classify(
        k,
        base,
        components,
        _base_incidence(components, n),
        frozenset(map(tuple, replay["counter"])),
        frozenset(map(tuple, replay["deleted"])),
        frozenset(map(tuple, replay["added"])),
    )


@lru_cache(maxsize=3)
def census_k(k: int) -> dict:
    if k not in (7, 8, 9):
        raise ValueError("the bounded L3 census is declared only for k=7,8,9")
    n, length = 3 * k + 2, k - 5
    base = _preserved(k)
    base_components = _components(base, n)
    base_edges = _base_incidence(base_components, n)
    window = {
        (row, column)
        for row in range(WINDOW_SIDE)
        for column in range(WINDOW_SIDE)
    }
    root_branch_centers = {
        vertex for vertex in window
        if vertex[0] == 0 and vertex[1] >= 2 or vertex[1] == 0
    } & base
    available_additions = window - base
    placements = [
        frozenset((row, start + offset) for offset in range(length))
        for row in range(WINDOW_SIDE)
        for start in range(WINDOW_SIDE - length + 1)
    ]

    counts = Counter()
    samples = {}
    realizations = []
    enumerated = 0
    admissible_placements = 0
    for counter in placements:
        counts["placements"] += 1
        if counter & base:
            counts["placement_uses_old_center"] += 1
            continue
        admissible_placements += 1
        addition_pool = sorted(available_additions - counter)
        for delete_count in range(1, MAX_DELETE + 1):
            for deleted_tuple in combinations(sorted(root_branch_centers), delete_count):
                deleted = frozenset(deleted_tuple)
                # Removing at least one endpoint is necessary to destroy the
                # original singleton support owner (0,1).
                if not ({(0, 0), (0, 2)} & deleted):
                    counts["deletion_keeps_old_attachment"] += 1
                    continue
                for added_tuple in combinations(addition_pool, delete_count):
                    added = frozenset(added_tuple)
                    enumerated += 1
                    reason, detail = _classify(
                        k, base, base_components, base_edges,
                        counter, deleted, added,
                    )
                    counts[reason] += 1
                    replay = {
                        "counter": [list(vertex) for vertex in sorted(counter)],
                        "deleted": [list(vertex) for vertex in sorted(deleted)],
                        "added": [list(vertex) for vertex in sorted(added)],
                    }
                    samples.setdefault(reason, {**replay, "detail": detail})
                    if reason == "realization":
                        realizations.append({**replay, **detail})

    return {
        "k": k,
        "n": n,
        "status": "realized" if realizations else "complete_negative_in_declared_grammar",
        "grammar": {
            "window": "rows 0..6, columns 0..6",
            "counter": f"every horizontal length-{length} interval wholly in the window",
            "counter_centers_must_all_be_new": True,
            "deletions": "1..3 old centers, only from the affine root or c=0 branch in the window",
            "deletion_must_include": "(0,0) or (0,2)",
            "compensating_additions": "same number as deletions, from other nonpreserved window vertices",
            "maximum_non_counter_edits": 2 * MAX_DELETE,
            "maximum_total_symmetric_difference": length + 2 * MAX_DELETE,
        },
        "search_space": {
            "placements": len(placements),
            "admissible_new_center_placements": admissible_placements,
            "fully_enumerated_edit_choices": enumerated,
        },
        "rejection_histogram": dict(sorted(counts.items())),
        "first_replay_by_terminal_status": dict(sorted(samples.items())),
        "realizations": realizations,
    }


def build_report() -> dict:
    records = [census_k(k) for k in (7, 8, 9)]
    return {
        "schema": SCHEMA,
        "checker": "residue_two_counter_interval_geometry_census",
        "status": (
            "realized" if all(record["status"] == "realized" for record in records)
            else "complete_negative_in_declared_grammar"
        ),
        "abstract_status": "counter surgery parent/count identities remain verified",
        "geometric_status": "bounded natural corner grammar exhausted",
        "records": records,
        "next_surgery_constraint": (
            "A next surgery must place the counter outside the 7x7 corner, let it replace "
            "old preserved centers, delete centers from components other than the root/branch, "
            "or obtain the +1 step from an existing interval endpoint. Merely adding up to "
            "three more root/branch edits cannot address a violating cell whose old preserved "
            "vertex belongs to another component."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    payload = json.dumps(build_report(), indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(payload)
    else:
        print(payload, end="")


if __name__ == "__main__":
    main()
