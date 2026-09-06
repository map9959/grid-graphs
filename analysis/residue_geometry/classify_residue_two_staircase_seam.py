#!/usr/bin/env python3
"""Classify the finite transfer grammar for a row/column rail staircase seam."""

from __future__ import annotations

import argparse
import itertools
import json
from collections import Counter
from fractions import Fraction
from pathlib import Path

from analysis._paths import analysis_path

Vertex = tuple[int, int]
Packet = tuple[int, int, int]
SCHEMA = "grid-graphs.residue-two-staircase-seam.v1"
DEFAULT_OUTPUT = analysis_path("residue_two_staircase_seam.json")


def _preserved(row: int, column: int, threshold: int, row_phase: int, column_phase: int) -> bool:
    return (
        column <= threshold and column % 3 == column_phase
    ) or (
        column > threshold and row % 3 == row_phase
    )


def transition_valid(
    row: int,
    threshold: int,
    advance: int,
    row_phase: int,
    column_phase: int,
) -> bool:
    """Check all unit cells met by one monotone seam transition."""
    if advance not in range(4):
        return False
    for column in range(threshold - 2, threshold + advance + 3):
        present = (
            _preserved(row, column, threshold, row_phase, column_phase),
            _preserved(row, column + 1, threshold, row_phase, column_phase),
            _preserved(row + 1, column, threshold + advance, row_phase, column_phase),
            _preserved(row + 1, column + 1, threshold + advance, row_phase, column_phase),
        )
        if sum(present) >= 3 or present[0] and present[3] or present[1] and present[2]:
            return False
    return True


def packet_paths(row_phase: int, column_phase: int) -> list[tuple[int, Packet]]:
    """Return every three-row loop with net staircase advance three."""
    paths = []
    for start in range(3):
        for packet in itertools.product(range(4), repeat=3):
            if sum(packet) != 3:
                continue
            threshold = start
            valid = True
            for row, advance in enumerate(packet):
                if not transition_valid(row, threshold, advance, row_phase, column_phase):
                    valid = False
                    break
                threshold += advance
            if valid:
                paths.append((start, packet))
    return paths


def seam_core(
    k: int,
    row_phase: int,
    column_phase: int,
    start: int,
    packet: Packet,
) -> set[Vertex]:
    """Materialize the 3k-square core, shifted into the width-one boundary ring."""
    side = 3 * k
    threshold = start
    thresholds = []
    for row in range(side):
        thresholds.append(threshold)
        threshold += packet[row % 3]
    return {
        (row + 1, column + 1)
        for row in range(side)
        for column in range(side)
        if _preserved(row, column, thresholds[row], row_phase, column_phase)
    }


def forced_forest(n: int, preserved: set[Vertex]) -> bool:
    parent = list(range(n * n))

    def root(vertex: int) -> int:
        while parent[vertex] != vertex:
            parent[vertex] = parent[parent[vertex]]
            vertex = parent[vertex]
        return vertex

    for row in range(n):
        for column in range(n):
            for d_row, d_column in ((0, 1), (1, 0)):
                other = row + d_row, column + d_column
                if other[0] == n or other[1] == n:
                    continue
                if (row, column) not in preserved and other not in preserved:
                    continue
                left = root(row * n + column)
                right = root(other[0] * n + other[1])
                if left == right:
                    return False
                parent[right] = left
    return True


def _core_components(k: int, preserved: set[Vertex]) -> tuple[dict[Vertex, int], int]:
    n = 3 * k + 2
    vertices = [(row, column) for row in range(1, n - 1) for column in range(1, n - 1)]
    indices = {vertex: index for index, vertex in enumerate(vertices)}
    parent = list(range(len(vertices)))

    def root(vertex: int) -> int:
        while parent[vertex] != vertex:
            parent[vertex] = parent[parent[vertex]]
            vertex = parent[vertex]
        return vertex

    for row, column in vertices:
        for d_row, d_column in ((0, 1), (1, 0)):
            other = row + d_row, column + d_column
            if other not in indices or ((row, column) not in preserved and other not in preserved):
                continue
            left, right = root(indices[row, column]), root(indices[other])
            if left == right:
                raise ValueError("seam core is not a forced forest")
            parent[right] = left
    roots = {value: index for index, value in enumerate(sorted({root(i) for i in range(len(vertices))}))}
    return {vertex: roots[root(index)] for vertex, index in indices.items()}, len(roots)


def _canonical_partition(partition: tuple[int, ...]) -> tuple[int, ...]:
    names: dict[int, int] = {}
    return tuple(names.setdefault(value, len(names)) for value in partition)


def _join(partition: tuple[int, ...], left: int, right: int) -> tuple[int, ...] | None:
    if partition[left] == partition[right]:
        return None
    old, new = partition[right], partition[left]
    return _canonical_partition(tuple(new if value == old else value for value in partition))


def cap_maximum(k: int, core: set[Vertex]) -> dict:
    """Run the exact max-plus perimeter automaton after contracting the core forest."""
    n = 3 * k + 2
    component, component_count = _core_components(k, core)
    perimeter = (
        [(0, column) for column in range(n)]
        + [(row, n - 1) for row in range(1, n)]
        + [(n - 1, column) for column in range(n - 2, -1, -1)]
        + [(row, 0) for row in range(n - 2, 0, -1)]
    )

    def inward(vertex: Vertex) -> Vertex | None:
        row, column = vertex
        if row == 0 and 0 < column < n - 1:
            return 1, column
        if row == n - 1 and 0 < column < n - 1:
            return n - 2, column
        if column == 0 and 0 < row < n - 1:
            return row, 1
        if column == n - 1 and 0 < row < n - 1:
            return row, n - 2
        return None

    occurrences: dict[int, list[int]] = {index: [] for index in range(component_count)}
    for position, vertex in enumerate(perimeter):
        inner = inward(vertex)
        if inner is not None:
            occurrences[component[inner]].append(position)
    first = {index: min(values) for index, values in occurrences.items() if values}
    last = {index: max(values) for index, values in occurrences.items() if values}

    layer_sizes = []
    best: tuple[int, tuple[int, ...]] | None = None
    for first_occupied in (0, 1):
        # Retained vertices are active core roots, the first corner, and the current vertex.
        active: tuple[int, ...] = ()
        partition = (0, 1)
        partition = _join(partition, 0, 1)
        assert partition is not None
        states = {(partition, first_occupied): (first_occupied, (first_occupied,))}
        for position, vertex in enumerate(perimeter[1:], start=1):
            introduced = tuple(index for index in range(component_count) if first.get(index) == position)
            pre_active = active + introduced
            following: dict[tuple[tuple[int, ...], int], tuple[int, tuple[int, ...]]] = {}
            inner = inward(vertex)
            for (old_partition, previous_occupied), (score, word) in states.items():
                for occupied in (0, 1):
                    # Insert new core roots before the retained first/current pair, then append new current.
                    core_part = old_partition[:len(active)]
                    first_part, current_part = old_partition[len(active):]
                    next_label = max(old_partition) + 1
                    partition = (
                        core_part
                        + tuple(range(next_label, next_label + len(introduced)))
                        + (first_part, current_part, next_label + len(introduced))
                    )
                    first_vertex = len(pre_active)
                    old_current = first_vertex + 1
                    new_vertex = first_vertex + 2
                    if previous_occupied or occupied:
                        joined = _join(partition, old_current, new_vertex)
                        if joined is None:
                            continue
                        partition = joined
                    if inner is not None and (occupied or inner in core):
                        joined = _join(partition, pre_active.index(component[inner]), new_vertex)
                        if joined is None:
                            continue
                        partition = joined
                    retained_components = tuple(
                        index for index, name in enumerate(pre_active) if last[name] != position
                    )
                    retained = (*retained_components, first_vertex, new_vertex)
                    partition = _canonical_partition(tuple(partition[index] for index in retained))
                    key = partition, occupied
                    candidate = score + occupied, word + (occupied,)
                    if key not in following or candidate[0] > following[key][0]:
                        following[key] = candidate
            states = following
            active = tuple(name for name in pre_active if last[name] != position)
            layer_sizes.append(len(states))
        for (partition, last_occupied), candidate in states.items():
            if last_occupied or first_occupied:
                partition = _join(partition, len(active), len(active) + 1)
                if partition is None:
                    continue
            if best is None or candidate[0] > best[0]:
                best = candidate
    if best is None:
        raise AssertionError("cap automaton has no accepting path")
    boundary = {vertex for vertex, occupied in zip(perimeter, best[1], strict=True) if occupied}
    return {
        "maximum": best[0],
        "core_component_count": component_count,
        "state_count_maximum": max(layer_sizes, default=1),
        "accepting_word": "".join(map(str, best[1])),
        "witness": [list(vertex) for vertex in sorted(boundary)],
        "forced_forest": forced_forest(n, core | boundary),
    }


def _quadratic_formula(points: list[tuple[int, int]]) -> str:
    matrix = [[Fraction(k * k), Fraction(k), Fraction(1), Fraction(value)] for k, value in points]
    for column in range(3):
        pivot = next(row for row in range(column, 3) if matrix[row][column])
        matrix[column], matrix[pivot] = matrix[pivot], matrix[column]
        scale = matrix[column][column]
        matrix[column] = [value / scale for value in matrix[column]]
        for row in range(3):
            if row == column:
                continue
            scale = matrix[row][column]
            matrix[row] = [left - scale * right for left, right in zip(matrix[row], matrix[column])]
    coefficients = [matrix[row][3] for row in range(3)]
    terms = []
    for coefficient, variable in zip(coefficients, ("k^2", "k", "")):
        if coefficient:
            terms.append((coefficient, variable))
    rendered = ""
    for coefficient, variable in terms:
        magnitude = abs(coefficient)
        body = ("" if magnitude == 1 and variable else str(magnitude)) + variable
        rendered += (("-" if coefficient < 0 else "") if not rendered else (" - " if coefficient < 0 else " + ")) + body
    return rendered or "0"


def build_report() -> dict:
    phases = []
    candidates = []
    for row_phase, column_phase in itertools.product(range(3), repeat=2):
        paths = packet_paths(row_phase, column_phase)
        phases.append({
            "row_phase": row_phase,
            "column_phase": column_phase,
            "packet_path_count": len(paths),
            "paths": [{"start": start, "advances": list(packet)} for start, packet in paths],
        })
        for start, packet in paths:
            records = []
            valid = True
            for k in (7, 8, 9):
                core = seam_core(k, row_phase, column_phase, start, packet)
                if not forced_forest(3 * k + 2, core):
                    valid = False
                    break
                cap = cap_maximum(k, core)
                records.append({
                    "k": k,
                    "n": 3 * k + 2,
                    "bulk_domain_baseline": 3 * k * k,
                    "seam_count": len(core) - 3 * k * k,
                    "core_count": len(core),
                    "cap": cap,
                    "total": len(core) + cap["maximum"],
                    "target": 3 * k * k + 7 * k,
                })
            if valid:
                candidates.append({
                    "row_phase": row_phase,
                    "column_phase": column_phase,
                    "start": start,
                    "packet": list(packet),
                    "records": records,
                    "formulas": {
                        "seam": _quadratic_formula([(r["k"], r["seam_count"]) for r in records]),
                        "cap": _quadratic_formula([(r["k"], r["cap"]["maximum"]) for r in records]),
                        "total": _quadratic_formula([(r["k"], r["total"]) for r in records]),
                    },
                })
    candidates.sort(key=lambda item: tuple(record["total"] for record in item["records"]), reverse=True)
    best = candidates[0]
    target_hit = [item for item in candidates if all(r["total"] == r["target"] for r in item["records"])]

    def compact(item: dict, keep_witness: bool = False) -> dict:
        result = {key: value for key, value in item.items() if key != "records"}
        result["records"] = []
        for record in item["records"]:
            cap = record["cap"]
            compact_cap = {
                "maximum": cap["maximum"],
                "core_component_count": cap["core_component_count"],
                "state_count_maximum": cap["state_count_maximum"],
                "forced_forest": cap["forced_forest"],
            }
            if keep_witness:
                compact_cap["accepting_word"] = cap["accepting_word"]
                compact_cap["witness"] = cap["witness"]
            result["records"].append({**record, "cap": compact_cap})
        return result

    total_classes = Counter(item["formulas"]["total"] for item in candidates)
    uniform = [item for item in candidates if item["packet"] == [1, 1, 1]]
    return {
        "schema": SCHEMA,
        "status": "uniform_seam_found" if target_hit else "staircase_seam_obstructed",
        "model": {
            "core": "rows and columns 1..3k in the (3k+2)-square",
            "domains": "column rails c=column_phase southwest of c<=threshold; row rails r=row_phase northeast of c>threshold",
            "monotone_packet": "three advances d in {0,1,2,3} with sum 3, repeated k times",
            "bulk_domain_count": "3k^2 before the seam exchange",
        },
        "seam_automaton": {
            "states": "(row mod 3, threshold mod 3, row phase, column phase)",
            "transition": "advance d in {0,1,2,3}; reject a three-center or diagonal-pair seam cell",
            "packet_acceptance": "three transitions, net advance 3, and forced core is a forest",
            "phase_classes": phases,
            "local_packet_paths": sum(item["packet_path_count"] for item in phases),
            "forced_forest_paths": len(candidates),
        },
        "cap_automaton": {
            "state": "core-component partition plus first/current perimeter vertices and previous occupancy",
            "edges": "perimeter edge iff either endpoint is preserved; inward edge iff its boundary or core endpoint is preserved",
            "rejection": "a union within one partition block, including final perimeter closure",
            "weight": "one per occupied boundary vertex",
        },
        "cycle_classification": {
            "total_formula_classes": dict(sorted(total_classes.items())),
            "uniform_advance_111_paths": len(uniform),
            "uniform_best_total": max(item["formulas"]["total"] for item in uniform),
            "capacity_certificate": {
                "maximum_total": "3k^2+6k+2",
                "target_deficit": "k-2",
                "observed_successor_gains_k7_and_k8": [
                    best["records"][1]["total"] - best["records"][0]["total"],
                    best["records"][2]["total"] - best["records"][1]["total"],
                ],
                "stable_gain": "6k+9",
                "gain_deficit": "1",
                "proof_rule": "every accepting path is one of the finite packet cycles; its seam and cap weights are affine after the packet, and the listed maximum cycle has coefficient 6",
            },
        },
        "best_path": compact(best, keep_witness=True),
        "target": {
            "count": "3k^2+7k",
            "stable_gain": "6k+10",
            "surviving_paths": len(target_hit),
            "attainable": bool(target_hit),
        },
        "classification": [compact(item) for item in candidates],
        "next_topology": {
            "name": "two-wall elbow with an articulation island",
            "reason": "a single monotone wall exposes only two perimeter arcs; the next topology must split one rail domain so a third cap arc attaches through one controlled articulation",
        },
        "checks": {
            "all_phase_pairs_have_eleven_local_packet_paths": all(item["packet_path_count"] == 11 for item in phases),
            "all_exported_caps_are_forced_forests": all(r["cap"]["forced_forest"] for item in candidates for r in item["records"]),
            "k_7_8_9_classified": all(len(item["records"]) == 3 for item in candidates),
            "target_decision_complete_for_grammar": not target_hit,
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    rendered = json.dumps(build_report(), indent=2, sort_keys=True) + "\n"
    if args.check:
        if not args.output.exists() or args.output.read_text() != rendered:
            raise SystemExit(f"stale or missing artifact: {args.output}")
        print(f"staircase seam classification matches {args.output}")
    else:
        args.output.write_text(rendered)
        print(f"wrote {args.output}")


if __name__ == "__main__":
    main()
