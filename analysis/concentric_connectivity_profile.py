#!/usr/bin/env python3
"""Exact rank and attachment profiles across concentric dual annuli."""

from __future__ import annotations

import argparse
import itertools
import json
from collections import Counter
from dataclasses import dataclass
from pathlib import Path

from diagonal_patterns import residue_two_affine_pattern, residue_two_explicit_pattern
from proof_oriented_identities import check_pattern_identities


SCHEMA = "grid-graphs.concentric-connectivity-profile.v1"
DEFAULT_OUTPUT = Path(__file__).with_name("concentric_connectivity_profile.json")
Face = str | tuple[int, int]


@dataclass(frozen=True, slots=True)
class PortWordSignature:
    repeated_components: int
    tokens: tuple[str, ...]
    runs: tuple[tuple[str, int], ...]


def port_word_signature(word: tuple[int, ...]) -> PortWordSignature:
    """Forget singleton names while retaining every repeated component exactly."""
    counts = Counter(word)
    repeated = {}
    tokens = []
    for label in word:
        if counts[label] == 1:
            tokens.append("S")
        else:
            repeated.setdefault(label, len(repeated))
            tokens.append(f"R{repeated[label]}")
    runs = []
    for token in tokens:
        if runs and runs[-1][0] == token:
            runs[-1] = (token, runs[-1][1] + 1)
        else:
            runs.append((token, 1))
    return PortWordSignature(len(repeated), tuple(tokens), tuple(runs))


class DSU:
    def __init__(self, items=()) -> None:
        self.parent = {item: item for item in items}

    def add(self, item) -> None:
        self.parent.setdefault(item, item)

    def find(self, item):
        parent = self.parent[item]
        if parent != item:
            self.parent[item] = self.find(parent)
        return self.parent[item]

    def union(self, left, right) -> bool:
        left = self.find(left)
        right = self.find(right)
        if left == right:
            return False
        self.parent[right] = left
        return True


def dual_edges(rows: tuple[str, ...]) -> tuple[tuple[Face, Face], ...]:
    n = len(rows)
    edges = []
    for row in range(n):
        for column in range(n - 1):
            if rows[row][column : column + 2] != "UU":
                continue
            edges.append(
                (
                    "OUT" if row == 0 else (row - 1, column),
                    "OUT" if row + 1 == n else (row, column),
                )
            )
    for row in range(n - 1):
        for column in range(n):
            if rows[row][column] != "U" or rows[row + 1][column] != "U":
                continue
            edges.append(
                (
                    "OUT" if column == 0 else (row, column - 1),
                    "OUT" if column + 1 == n else (row, column),
                )
            )
    return tuple(edges)


def _depth(face: Face, face_side: int) -> int:
    if face == "OUT":
        return -1
    row, column = face
    return min(row, column, face_side - 1 - row, face_side - 1 - column)


def _ring_order(face: tuple[int, int], depth: int, face_side: int) -> int:
    row, column = face
    low = depth
    high = face_side - 1 - depth
    side = high - low + 1
    if row == low:
        return column - low
    if column == high:
        return side - 1 + row - low
    if row == high:
        return 3 * (side - 1) - (column - low)
    if column == low:
        return 4 * (side - 1) - (row - low)
    raise ValueError("face is not on the requested ring")


def outward_annulus_profile(rows: tuple[str, ...]) -> dict:
    n = len(rows)
    face_side = n - 1
    faces = tuple((row, column) for row in range(face_side) for column in range(face_side))
    edges = dual_edges(rows)
    maximum_depth = max((_depth(face, face_side) for face in faces), default=-1)
    dsu = DSU(("OUT",))
    exposed = {"OUT"}
    total_rank = total_cycles = 0
    stages = []
    for depth in range(maximum_depth + 1):
        new_faces = tuple(face for face in faces if _depth(face, face_side) == depth)
        before_roots = {dsu.find(face) for face in exposed}
        out_root_before = dsu.find("OUT")
        old_labels = {out_root_before: 0}
        for root in sorted(before_roots - {out_root_before}, key=repr):
            old_labels[root] = len(old_labels)
        for face in new_faces:
            dsu.add(face)
            exposed.add(face)
        stage_edges = tuple(
            edge
            for edge in edges
            if max(_depth(edge[0], face_side), _depth(edge[1], face_side)) == depth
        )
        crossing = []
        touched_old_roots = set()
        for left, right in stage_edges:
            left_depth = _depth(left, face_side)
            right_depth = _depth(right, face_side)
            if left_depth < depth == right_depth:
                old, new = left, right
            elif right_depth < depth == left_depth:
                old, new = right, left
            else:
                continue
            root = dsu.find(old)
            touched_old_roots.add(root)
            crossing.append((new, old_labels[root]))
        sealed = before_roots - touched_old_roots - {out_root_before}
        rank_added = cycles_added = 0
        for left, right in stage_edges:
            if dsu.union(left, right):
                rank_added += 1
            else:
                cycles_added += 1
        after_roots = {dsu.find(face) for face in exposed}
        expected_rank = len(new_faces) + len(before_roots) - len(after_roots)
        if rank_added != expected_rank or rank_added + cycles_added != len(stage_edges):
            raise AssertionError("annulus rank accounting failed")
        total_rank += rank_added
        total_cycles += cycles_added
        crossing.sort(key=lambda item: (_ring_order(item[0], depth, face_side), item[1]))
        stages.append(
            {
                "depth": depth,
                "new_faces": len(new_faces),
                "edges_added": len(stage_edges),
                "components_before": len(before_roots),
                "components_after": len(after_roots),
                "attachment_debt_before": len(before_roots) - 1,
                "attachment_debt_after": len(after_roots) - 1,
                "crossing_ports": len(crossing),
                "distinct_old_port_components": len({label for _, label in crossing}),
                "ordered_old_component_word": [label for _, label in crossing],
                "sealed_non_out_components": len(sealed),
                "rank_added": rank_added,
                "cycles_added": cycles_added,
                "merge_rank": rank_added - len(new_faces),
            }
        )
    identities = check_pattern_identities(list(rows))
    if total_rank != identities.graphic_rank or total_cycles != identities.cycle_rank:
        raise AssertionError("annulus totals disagree with whole-pattern identities")
    return {
        "total_rank": total_rank,
        "total_cycles": total_cycles,
        "final_components": identities.components,
        "maximum_attachment_debt": max(
            (stage["attachment_debt_after"] for stage in stages), default=0
        ),
        "all_stages_unsealed": all(
            stage["sealed_non_out_components"] == 0 for stage in stages
        ),
        "stages": stages,
    }


def _run_count(lines: tuple[str, ...]) -> int:
    return sum(
        value == "U" and (index == 0 or line[index - 1] != "U")
        for line in lines
        for index, value in enumerate(line)
    )


def centered_prefix_profile(rows: tuple[str, ...]) -> list[dict]:
    n = len(rows)
    profiles = []
    for side in range(2 if n % 2 == 0 else 3, n + 1, 2):
        offset = (n - side) // 2
        square = tuple(row[offset : offset + side] for row in rows[offset : offset + side])
        u_count = sum(row.count("U") for row in square)
        transposed = tuple("".join(square[row][column] for row in range(side)) for column in range(side))
        runs = _run_count(square) + _run_count(transposed)
        induced_edges = 2 * u_count - runs
        perimeter = (
            square[0]
            + "".join(row[-1] for row in square[1:])
            + square[-1][-2::-1]
            + "".join(row[0] for row in square[-2:0:-1])
        )
        perimeter_ports = sum(
            perimeter[index] == perimeter[(index + 1) % len(perimeter)] == "U"
            for index in range(len(perimeter))
        )
        face_side = side - 1
        faces = tuple((row, column) for row in range(face_side) for column in range(face_side))
        dsu = DSU(faces)
        internal_edges = []
        for row in range(1, side - 1):
            for column in range(side - 1):
                if square[row][column : column + 2] == "UU":
                    internal_edges.append(((row - 1, column), (row, column)))
        for row in range(side - 1):
            for column in range(1, side - 1):
                if square[row][column] == square[row + 1][column] == "U":
                    internal_edges.append(((row, column - 1), (row, column)))
        rank = sum(dsu.union(left, right) for left, right in internal_edges)
        components = len({dsu.find(face) for face in faces})
        cycles = len(internal_edges) - rank
        face_count = face_side * face_side
        attachment_surplus = perimeter_ports - components
        if induced_edges - face_count != attachment_surplus + cycles:
            raise AssertionError("centered attachment identity failed")
        port_roots = set()
        ordered_port_roots = []
        for column in range(side - 1):
            if square[0][column : column + 2] == "UU":
                root = dsu.find((0, column))
                port_roots.add(root)
                ordered_port_roots.append(root)
        for row in range(side - 1):
            if square[row][-1] == square[row + 1][-1] == "U":
                root = dsu.find((row, side - 2))
                port_roots.add(root)
                ordered_port_roots.append(root)
        for column in reversed(range(side - 1)):
            if square[-1][column : column + 2] == "UU":
                root = dsu.find((side - 2, column))
                port_roots.add(root)
                ordered_port_roots.append(root)
        for row in reversed(range(side - 1)):
            if square[row][0] == square[row + 1][0] == "U":
                root = dsu.find((row, 0))
                port_roots.add(root)
                ordered_port_roots.append(root)
        labels = {}
        port_word = []
        for root in ordered_port_roots:
            labels.setdefault(root, len(labels))
            port_word.append(labels[root])
        occurrences = Counter(port_word)
        signature = port_word_signature(tuple(port_word))
        cyclic_runs = {
            label: max(
                1,
                sum(
                    observed == label and port_word[index - 1] != label
                    for index, observed in enumerate(port_word)
                ),
            )
            for label in occurrences
        }
        profiles.append(
            {
                "side": side,
                "u_count": u_count,
                "run_sum": runs,
                "induced_u_edges": induced_edges,
                "face_count": face_count,
                "internal_components": components,
                "perimeter_ports": perimeter_ports,
                "ported_components": len(port_roots),
                "sealed_components": components - len(port_roots),
                "canonical_cyclic_port_word": port_word,
                "repeated_port_components": sum(
                    count > 1 for count in occurrences.values()
                ),
                "maximum_port_occurrences": max(occurrences.values(), default=0),
                "maximum_cyclic_port_runs": max(cyclic_runs.values(), default=0),
                "compressed_port_tokens": list(signature.tokens),
                "compressed_port_runs": [list(item) for item in signature.runs],
                "compressed_port_run_count": len(signature.runs),
                "attachment_surplus": attachment_surplus,
                "internal_cycles": cycles,
                "identity_excess": induced_edges - face_count,
            }
        )
    return profiles


def analyze_pattern(rows: tuple[str, ...]) -> dict:
    identities = check_pattern_identities(list(rows))
    annuli = outward_annulus_profile(rows)
    centered = centered_prefix_profile(rows)
    if identities.components == 1 and any(item["sealed_components"] for item in centered):
        raise AssertionError("connected witness has a sealed centered component")
    return {
        "n": len(rows),
        "u_count": identities.u_count,
        "dual_edges": identities.dual_edges,
        "dual_vertices": identities.dual_vertices,
        "graphic_rank": identities.graphic_rank,
        "cycle_rank": identities.cycle_rank,
        "components": identities.components,
        "outward_annuli": annuli,
        "centered_prefixes": centered,
    }


def n5_scalar_maximum_census() -> dict:
    n = 5
    outer = tuple(
        (row, column)
        for row in range(n)
        for column in range(n)
        if row in (0, n - 1) or column in (0, n - 1)
    )
    inner_boundary = tuple(
        (row, column)
        for row in range(1, 4)
        for column in range(1, 4)
        if row in (1, 3) or column in (1, 3)
    )
    rank_histogram = Counter()
    component_histogram = Counter()
    maximum_rank = -1
    best_rows = None
    connected = 0
    for chosen in itertools.combinations(outer, 4):
        grid = [["." for _ in range(n)] for _ in range(n)]
        for row, column in (*inner_boundary, *chosen):
            grid[row][column] = "U"
        rows = tuple("".join(row) for row in grid)
        identities = check_pattern_identities(list(rows))
        rank_histogram[identities.graphic_rank] += 1
        component_histogram[identities.components] += 1
        connected += identities.components == 1
        if identities.graphic_rank > maximum_rank:
            maximum_rank = identities.graphic_rank
            best_rows = rows
    required_rank = (n - 1) ** 2
    return {
        "patterns": sum(rank_histogram.values()),
        "layer_full_counts": {"side_5_boundary": 12, "side_3_boundary": 0, "center": 1},
        "connected_patterns": connected,
        "required_rank": required_rank,
        "maximum_rank": maximum_rank,
        "minimum_component_count": 1 + required_rank - maximum_rank,
        "rank_histogram": {str(key): value for key, value in sorted(rank_histogram.items())},
        "component_histogram": {
            str(key): value for key, value in sorted(component_histogram.items())
        },
        "rank_maximizing_pattern": list(best_rows or ()),
    }


def _phase_rows() -> tuple[str, ...]:
    path = Path(__file__).with_name("residue_two_phase_front_witness.txt")
    return tuple(
        line.strip()
        for line in path.read_text().splitlines()
        if line.strip() and not line.startswith("#")
    )


def build_artifact() -> dict:
    patterns = {
        f"n{n}-exact": tuple(residue_two_explicit_pattern(n)) for n in (5, 8, 11, 14)
    }
    patterns["n17-affine"] = tuple(residue_two_affine_pattern(17))
    patterns["n20-phase"] = _phase_rows()
    witnesses = {name: analyze_pattern(rows) for name, rows in patterns.items()}
    feasible_prefixes = [
        prefix
        for witness in witnesses.values()
        for prefix in witness["centered_prefixes"]
    ]
    rank_census_path = Path(__file__).with_name("concentric_layer_rank_census.json")
    rank_census = json.loads(rank_census_path.read_text())
    scalar_controls = {}
    for name, item in rank_census["cases"].items():
        scalar_controls[name] = {
            "rank_maximizing_pattern": analyze_pattern(
                tuple(item["rank_maximizing_pattern"])
            ),
            "maximum_edge_pattern": analyze_pattern(
                tuple(item["maximum_edge_pattern"])
            ),
        }
    return {
        "schema": SCHEMA,
        "scope": {
            "semantics": "exact-pattern-profiles-and-exhaustive-n5-layer-control",
            "arbitrary_width_bound_claimed": False,
        },
        "identity": {
            "formula": "M_s-(s-1)^2=(q_s-d_s)+beta_s",
            "terms": {
                "M_s": "U-U edges induced by the centered primal square",
                "q_s": "active U-U perimeter edge ports",
                "d_s": "internal dual components before exterior attachment",
                "beta_s": "internal dual cycle rank",
            },
        },
        "witnesses": witnesses,
        "observed_feasible_port_signature_bounds": {
            "maximum_repeated_components": max(
                item["repeated_port_components"] for item in feasible_prefixes
            ),
            "maximum_cyclic_runs_per_component": max(
                item["maximum_cyclic_port_runs"] for item in feasible_prefixes
            ),
            "maximum_compressed_runs": max(
                item["compressed_port_run_count"] for item in feasible_prefixes
            ),
            "scope": "known feasible witnesses n=5,8,11,14,17,20 only",
        },
        "scalar_optimum_controls": scalar_controls,
        "n5_scalar_maximum_census": n5_scalar_maximum_census(),
        "conclusion": (
            "The n=5 and n=8 scalar optima are unrealizable by exact census. On "
            "known feasible witnesses, ordered port partitions compress to at most "
            "four repeated components, three cyclic runs per component, and nine "
            "compressed runs; proving these bounds for all extremal patterns is the "
            "remaining annulus-state coverage problem."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    rendered = json.dumps(build_artifact(), indent=2, sort_keys=True) + "\n"
    if args.check:
        if not args.output.exists() or args.output.read_text() != rendered:
            raise SystemExit(f"stale or missing artifact: {args.output}")
        print(f"concentric connectivity profile matches {args.output}")
    else:
        args.output.write_text(rendered)
        print(rendered, end="")


if __name__ == "__main__":
    main()
