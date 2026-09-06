#!/usr/bin/env python3
"""Compare residue construction families with independent graph metrics."""

from __future__ import annotations

import argparse
import csv
import sys
from collections import Counter, defaultdict
from dataclasses import dataclass
from typing import Callable, Iterable

from analysis.patterns.diagonal_patterns import (
    q_formula,
    residue_one_pattern,
    residue_two_affine_pattern,
    residue_two_explicit_pattern,
    residue_zero_phase_pattern,
)
from analysis._paths import analysis_path


Face = tuple[int, int] | str


@dataclass
class Metrics:
    family: str
    n: int
    residue: int
    u_count: int
    q: int
    surplus: int
    row_runs: int
    column_runs: int
    edges: int
    dual_vertices: int
    components: int
    component_sizes: list[int]
    graphic_rank: int
    component_cycle_ranks: list[int]
    cycle_rank: int
    out_component_size: int
    out_edges: int
    packet_histograms: list[Counter[int]] | None


def run_count(lines: Iterable[str]) -> int:
    """Count maximal U-runs without relying on the induced-edge enumeration."""
    return sum(
        ch == "U" and (i == 0 or line[i - 1] != "U")
        for line in lines
        for i, ch in enumerate(line)
    )


def dual_edge_for_horizontal(n: int, row: int, column: int) -> tuple[Face, Face]:
    if row == 0:
        return "OUT", (0, column)
    if row == n - 1:
        return (n - 2, column), "OUT"
    return (row - 1, column), (row, column)


def dual_edge_for_vertical(n: int, row: int, column: int) -> tuple[Face, Face]:
    if column == 0:
        return "OUT", (row, 0)
    if column == n - 1:
        return (row, n - 2), "OUT"
    return (row, column - 1), (row, column)


def packet_histograms(rows: list[str]) -> list[Counter[int]] | None:
    """Return row histograms for the boundary-trimmed three-cell interior."""
    n = len(rows)
    if (n - 2) % 3:
        return None
    return [
        Counter(packet.count("U") - 2 for packet in (row[i : i + 3] for i in range(1, n - 1, 3)))
        for row in rows
    ]


def analyze(family: str, rows: list[str]) -> Metrics:
    n = len(rows)
    if n < 2 or any(len(row) != n or set(row) - {".", "U"} for row in rows):
        raise ValueError(f"{family}: pattern must be a square .U grid")

    faces: list[Face] = ["OUT", *((r, c) for r in range(n - 1) for c in range(n - 1))]
    adjacency: dict[Face, list[Face]] = defaultdict(list)
    edges: list[tuple[Face, Face]] = []
    for r, row in enumerate(rows):
        for c in range(n - 1):
            if row[c] == row[c + 1] == "U":
                edges.append(dual_edge_for_horizontal(n, r, c))
    for r in range(n - 1):
        for c in range(n):
            if rows[r][c] == rows[r + 1][c] == "U":
                edges.append(dual_edge_for_vertical(n, r, c))
    for left, right in edges:
        adjacency[left].append(right)
        adjacency[right].append(left)

    unseen = set(faces)
    component_data: list[tuple[int, int, bool]] = []
    while unseen:
        start = min(unseen, key=str)
        stack = [start]
        unseen.remove(start)
        vertices: set[Face] = set()
        degree_sum = 0
        while stack:
            face = stack.pop()
            vertices.add(face)
            degree_sum += len(adjacency[face])
            for neighbor in adjacency[face]:
                if neighbor in unseen:
                    unseen.remove(neighbor)
                    stack.append(neighbor)
        size = len(vertices)
        edge_count = degree_sum // 2
        component_data.append((size, edge_count - size + 1, "OUT" in vertices))

    component_data.sort(key=lambda item: (item[0], item[1], item[2]))
    u_count = sum(row.count("U") for row in rows)
    row_runs = run_count(rows)
    columns = ["".join(rows[r][c] for r in range(n)) for c in range(n)]
    column_runs = run_count(columns)
    if len(edges) != 2 * u_count - row_runs - column_runs:
        raise AssertionError(f"{family}: induced-edge/run identity failed")

    components = len(component_data)
    vertices = len(faces)
    cycle_rank = len(edges) - vertices + components
    component_ranks = [item[1] for item in component_data]
    if cycle_rank != sum(component_ranks):
        raise AssertionError(f"{family}: component cycle ranks do not add up")

    return Metrics(
        family=family,
        n=n,
        residue=n % 3,
        u_count=u_count,
        q=q_formula(n),
        surplus=u_count - q_formula(n),
        row_runs=row_runs,
        column_runs=column_runs,
        edges=len(edges),
        dual_vertices=vertices,
        components=components,
        component_sizes=[item[0] for item in component_data],
        graphic_rank=vertices - components,
        component_cycle_ranks=component_ranks,
        cycle_rank=cycle_rank,
        out_component_size=next(item[0] for item in component_data if item[2]),
        out_edges=sum("OUT" in edge for edge in edges),
        packet_histograms=packet_histograms(rows),
    )


def assert_family_formulas(metric: Metrics) -> None:
    n = metric.n
    if metric.family == "residue-one":
        k = (n - 1) // 3
        expected = {
            "u_count": 6 * k * k + k + 1,
            "row_runs": 3 * k,
            "column_runs": 3 * k * k - k + 2,
            "edges": 9 * k * k,
        }
    elif metric.family == "residue-zero-phase":
        k = n // 3
        expected = {
            "u_count": 6 * k * k - 3 * k + 2,
            "row_runs": 3 * k * k - 6 * k + 6,
            "column_runs": 6 * k - 4,
            "edges": 9 * k * k - 6 * k + 2,
        }
    else:
        return
    for field, value in expected.items():
        actual = getattr(metric, field)
        if actual != value:
            raise AssertionError(f"{metric.family} n={n}: {field}={actual}, expected {value}")


def recurrence_result(n: int) -> str:
    difference = q_formula(n + 3) - q_formula(n)
    expected = 4 * n + 3 + int(n == 14)
    if difference != expected:
        raise AssertionError(f"q recurrence failed at n={n}: {difference} != {expected}")
    return f"q({n + 3})-q({n})={difference}=4n+3"


def compact_list(values: Iterable[int]) -> str:
    return ";".join(map(str, values))


def metric_record(metric: Metrics) -> dict[str, object]:
    return {
        "family": metric.family,
        "n": metric.n,
        "residue": metric.residue,
        "U": metric.u_count,
        "q": metric.q,
        "surplus": metric.surplus,
        "row_runs": metric.row_runs,
        "column_runs": metric.column_runs,
        "UU_edges": metric.edges,
        "dual_vertices": metric.dual_vertices,
        "components": metric.components,
        "component_sizes": compact_list(metric.component_sizes),
        "graphic_rank": metric.graphic_rank,
        "component_cycle_ranks": compact_list(metric.component_cycle_ranks),
        "E-V+components": metric.cycle_rank,
        "OUT_component_size": metric.out_component_size,
        "boundary_OUT_edges": metric.out_edges,
    }


def print_detail(metrics: list[Metrics]) -> None:
    for metric in metrics:
        print(f"[{metric.family} n={metric.n} residue={metric.residue}]")
        print(
            f"U={metric.u_count} q={metric.q} surplus={metric.surplus} "
            f"row_runs={metric.row_runs} column_runs={metric.column_runs} "
            f"UU_edges={metric.edges}"
        )
        print(
            f"dual_vertices={metric.dual_vertices} components={metric.components} "
            f"component_sizes={metric.component_sizes} graphic_rank={metric.graphic_rank}"
        )
        print(
            f"component_cycle_ranks={metric.component_cycle_ranks} "
            f"E-V+components={metric.cycle_rank} OUT_component_size={metric.out_component_size} "
            f"boundary_OUT_edges={metric.out_edges}"
        )
        print(f"recurrence: {recurrence_result(metric.n)} [ok]")
        if metric.packet_histograms is None:
            print("packet_charge: n/a (columns 1..n-2 do not split into 3-cells)")
        else:
            print("packet_charge (columns 1..n-2, charge=|U|-2):")
            for row, histogram in enumerate(metric.packet_histograms):
                values = ",".join(f"{charge}:{histogram[charge]}" for charge in sorted(histogram))
                print(f"  row {row}: {values}")


def print_table(metrics: list[Metrics]) -> None:
    fields = list(metric_record(metrics[0]))
    records = [[str(metric_record(metric)[field]) for field in fields] for metric in metrics]
    widths = [max(len(field), *(len(record[i]) for record in records)) for i, field in enumerate(fields)]
    print(" ".join(field.ljust(widths[i]) for i, field in enumerate(fields)))
    for record in records:
        print(" ".join(value.ljust(widths[i]) for i, value in enumerate(record)))


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--residue-one", nargs="*", type=int, default=[13], metavar="N")
    parser.add_argument("--residue-zero", nargs="*", type=int, default=[21], metavar="N")
    parser.add_argument("--residue-two", nargs="*", type=int, default=[14], metavar="N")
    parser.add_argument("--affine", nargs="*", type=int, default=[17], metavar="N")
    parser.add_argument(
        "--near",
        nargs="*",
        choices=("phasecrop", "pump", "macro"),
        default=[],
        help="also analyze fixed n=17 near patterns",
    )
    parser.add_argument("--middle-250", action="store_true", help="analyze the cached n=20 grammar witness")
    parser.add_argument(
        "--phase-front-250",
        action="store_true",
        help="analyze the unicyclic n=20 phase-front witness",
    )
    parser.add_argument("--format", choices=("detail", "table", "csv"), default="detail")
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    requests: list[tuple[str, int, Callable[[int], list[str]]]] = []
    requests.extend(("residue-one", n, residue_one_pattern) for n in args.residue_one)
    requests.extend(("residue-zero-phase", n, residue_zero_phase_pattern) for n in args.residue_zero)
    requests.extend(("residue-two-cached", n, residue_two_explicit_pattern) for n in args.residue_two)
    requests.extend(("residue-two-affine", n, residue_two_affine_pattern) for n in args.affine)

    metrics = [analyze(family, generator(n)) for family, n, generator in requests]
    if args.near:
        from analysis.searches.search_residue_two_near import NEAR_MACRO, NEAR_PHASECROP, NEAR_PUMP

        near_patterns = {"phasecrop": NEAR_PHASECROP, "pump": NEAR_PUMP, "macro": NEAR_MACRO}
        metrics.extend(analyze(f"residue-two-near-{name}", list(near_patterns[name])) for name in args.near)
    if args.middle_250:
        from analysis.searches.search_residue_two_middle import KNOWN_250

        metrics.append(analyze("residue-two-middle-250", list(KNOWN_250)))
    if args.phase_front_250:
        

        rows = analysis_path("residue_two_phase_front_witness.txt").read_text().splitlines()
        metrics.append(analyze("residue-two-phase-front-250", rows))

    if not metrics:
        raise SystemExit("no constructions selected")
    for metric in metrics:
        recurrence_result(metric.n)
        assert_family_formulas(metric)

    if args.format == "detail":
        print_detail(metrics)
    elif args.format == "table":
        print_table(metrics)
    else:
        writer = csv.DictWriter(sys.stdout, fieldnames=list(metric_record(metrics[0])))
        writer.writeheader()
        writer.writerows(metric_record(metric) for metric in metrics)


if __name__ == "__main__":
    main()
