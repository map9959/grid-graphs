#!/usr/bin/env python3
"""Classify the minimal two-wall elbow/island residue-two transfer grammar."""

from __future__ import annotations

import argparse
import itertools
import json
from collections import Counter
from pathlib import Path

from analysis._paths import analysis_path
from analysis.residue_geometry.classify_residue_two_staircase_seam import (
    _quadratic_formula,
    cap_maximum,
    forced_forest,
)

Vertex = tuple[int, int]
Packet = tuple[int, int, int]
SCHEMA = "grid-graphs.residue-two-elbow-island.v1"
DEFAULT_OUTPUT = analysis_path("residue_two_elbow_island.json")
WIDTH_CAP = 2


def wall_packet_cycles(width_cap: int = WIDTH_CAP) -> list[tuple[Packet, Packet, int, tuple[int, int, int]]]:
    """Enumerate two noncrossing three-step wall cycles, not board configurations."""
    packets = [packet for packet in itertools.product(range(4), repeat=3) if sum(packet) == 3]
    cycles = []
    for lower, upper, initial_width in itertools.product(packets, packets, range(1, width_cap + 1)):
        width = initial_width
        widths = []
        valid = True
        for lower_advance, upper_advance in zip(lower, upper, strict=True):
            widths.append(width)
            width += upper_advance - lower_advance
            if not 1 <= width <= width_cap:
                valid = False
                break
        if valid and width == initial_width:
            cycles.append((lower, upper, initial_width, tuple(widths)))
    return cycles


def _owned(
    row: int,
    column: int,
    lower: int,
    upper: int,
    row_phase: int,
    column_phase: int,
    island_phase: int,
    island_orientation: str,
) -> tuple[bool, str]:
    if column <= lower:
        return column % 3 == column_phase, "vertical-domain"
    if column <= upper:
        phase = row if island_orientation == "H" else column
        return phase % 3 == island_phase, "island"
    return row % 3 == row_phase, "horizontal-domain"


def transition_valid(
    row: int,
    lower: int,
    width: int,
    lower_advance: int,
    upper_advance: int,
    row_phase: int,
    column_phase: int,
    island_phase: int,
    island_orientation: str,
) -> bool:
    next_lower = lower + lower_advance
    next_upper = lower + width + upper_advance
    if not 1 <= next_upper - next_lower <= WIDTH_CAP:
        return False
    for column in range(min(lower, next_lower) - 2, max(lower + width, next_upper) + 3):
        present = (
            _owned(row, column, lower, lower + width, row_phase, column_phase,
                   island_phase, island_orientation)[0],
            _owned(row, column + 1, lower, lower + width, row_phase, column_phase,
                   island_phase, island_orientation)[0],
            _owned(row + 1, column, next_lower, next_upper, row_phase, column_phase,
                   island_phase, island_orientation)[0],
            _owned(row + 1, column + 1, next_lower, next_upper, row_phase, column_phase,
                   island_phase, island_orientation)[0],
        )
        if sum(present) >= 3 or present[0] and present[3] or present[1] and present[2]:
            return False
    return True


def local_paths() -> list[dict]:
    paths = []
    for orientation in ("H", "V"):
        for row_phase, column_phase in itertools.product(range(3), repeat=2):
            host_phase = row_phase if orientation == "H" else column_phase
            for island_phase in sorted(set(range(3)) - {host_phase}):
                for start in range(3):
                    for lower, upper, initial_width, widths in wall_packet_cycles():
                        threshold = start
                        if all(
                            transition_valid(
                                row,
                                threshold + sum(lower[:row]),
                                widths[row],
                                lower[row],
                                upper[row],
                                row_phase,
                                column_phase,
                                island_phase,
                                orientation,
                            )
                            for row in range(3)
                        ):
                            paths.append({
                                "orientation": orientation,
                                "row_phase": row_phase,
                                "column_phase": column_phase,
                                "island_phase": island_phase,
                                "start": start,
                                "lower_packet": lower,
                                "upper_packet": upper,
                                "initial_width": initial_width,
                                "width_cycle": widths,
                            })
    return paths


def materialize(k: int, path: dict) -> tuple[set[Vertex], set[Vertex], set[Vertex]]:
    side = 3 * k
    lower = path["start"]
    upper = lower + path["initial_width"]
    preserved: set[Vertex] = set()
    island: set[Vertex] = set()
    exterior: set[Vertex] = set()
    for row in range(side):
        packet_row = row % 3
        for column in range(side):
            keep, owner = _owned(
                row,
                column,
                lower,
                upper,
                path["row_phase"],
                path["column_phase"],
                path["island_phase"],
                path["orientation"],
            )
            if keep:
                vertex = row + 1, column + 1
                preserved.add(vertex)
                (island if owner == "island" else exterior).add(vertex)
        lower += path["lower_packet"][packet_row]
        upper += path["upper_packet"][packet_row]
    return preserved, island, exterior


def unit_cells_valid(n: int, preserved: set[Vertex]) -> bool:
    for row in range(n - 1):
        for column in range(n - 1):
            present = (
                (row, column) in preserved,
                (row, column + 1) in preserved,
                (row + 1, column) in preserved,
                (row + 1, column + 1) in preserved,
            )
            if sum(present) >= 3 or present[0] and present[3] or present[1] and present[2]:
                return False
    return True


def _forced_support(n: int, centers: set[Vertex]) -> set[Vertex]:
    support = set(centers)
    for row, column in centers:
        for d_row, d_column in ((-1, 0), (1, 0), (0, -1), (0, 1)):
            neighbor = row + d_row, column + d_column
            if 0 <= neighbor[0] < n and 0 <= neighbor[1] < n:
                support.add(neighbor)
    return support


def articulation_data(n: int, island: set[Vertex], exterior: set[Vertex]) -> dict:
    intersection = sorted(_forced_support(n, island) & _forced_support(n, exterior))
    return {
        "intersection_size": len(intersection),
        "singleton": len(intersection) == 1,
        "vertex": list(intersection[0]) if len(intersection) == 1 else None,
    }


def boundary_domain_arcs(k: int, path: dict) -> dict:
    """Count maximal ownership arcs on the inner boundary, cyclically."""
    side = 3 * k
    lower = path["start"]
    lowers = []
    uppers = []
    for row in range(side):
        lowers.append(lower)
        uppers.append(lower + path["width_cycle"][row % 3])
        lower += path["lower_packet"][row % 3]
    perimeter = (
        [(0, column) for column in range(side)]
        + [(row, side - 1) for row in range(1, side)]
        + [(side - 1, column) for column in range(side - 2, -1, -1)]
        + [(row, 0) for row in range(side - 2, 0, -1)]
    )
    labels = [
        _owned(
            row,
            column,
            lowers[row],
            uppers[row],
            path["row_phase"],
            path["column_phase"],
            path["island_phase"],
            path["orientation"],
        )[1]
        for row, column in perimeter
    ]
    starts = [index for index, label in enumerate(labels) if label != labels[index - 1]]
    by_owner = Counter(labels[index] for index in starts)
    return {
        "count": len(starts),
        "by_owner": dict(sorted(by_owner.items())),
        "three_arcs": len(starts) == 3,
    }


def _serialize_path(path: dict) -> dict:
    return {
        key: list(value) if isinstance(value, tuple) else value
        for key, value in path.items()
    }


def build_report() -> dict:
    paths = local_paths()
    evaluated = []
    cap_cache: dict[tuple[int, frozenset[Vertex]], dict] = {}
    rejection = Counter()
    minimum_intersection: int | None = None
    minimum_example = None

    for path in paths:
        records = []
        accepted_geometry = True
        for k in (7, 8, 9):
            n = 3 * k + 2
            core, island, exterior = materialize(k, path)
            if not island:
                rejection["empty_island"] += 1
                accepted_geometry = False
                break
            if not unit_cells_valid(n, core):
                rejection["unit_cell"] += 1
                accepted_geometry = False
                break
            if not forced_forest(n, core):
                rejection["forced_cycle"] += 1
                accepted_geometry = False
                break
            articulation = articulation_data(n, island, exterior)
            arcs = boundary_domain_arcs(k, path)
            if minimum_intersection is None or articulation["intersection_size"] < minimum_intersection:
                minimum_intersection = articulation["intersection_size"]
                minimum_example = {"path": _serialize_path(path), "k": k, **articulation}
            cache_key = k, frozenset(core)
            if cache_key not in cap_cache:
                cap_cache[cache_key] = cap_maximum(k, core)
            cap = cap_cache[cache_key]
            records.append({
                "k": k,
                "core_count": len(core),
                "island_count": len(island),
                "seam_correction": len(core) - 3 * k * k,
                "articulation": articulation,
                "boundary_domain_arcs": arcs,
                "cap_maximum": cap["maximum"],
                "cap_forced_forest": cap["forced_forest"],
                "unit_cells_valid": True,
                "core_forced_forest": True,
                "total": len(core) + cap["maximum"],
                "target": 3 * k * k + 7 * k,
            })
        if accepted_geometry:
            evaluated.append({
                "path": _serialize_path(path),
                "records": records,
                "formulas": {
                    "seam": _quadratic_formula([(r["k"], r["seam_correction"]) for r in records]),
                    "island": _quadratic_formula([(r["k"], r["island_count"]) for r in records]),
                    "cap": _quadratic_formula([(r["k"], r["cap_maximum"]) for r in records]),
                    "total": _quadratic_formula([(r["k"], r["total"]) for r in records]),
                },
            })

    evaluated.sort(key=lambda item: tuple(record["total"] for record in item["records"]), reverse=True)
    best = evaluated[0]
    singleton = [
        item for item in evaluated
        if all(record["articulation"]["singleton"] for record in item["records"])
    ]
    three_arcs = [
        item for item in evaluated
        if all(record["boundary_domain_arcs"]["three_arcs"] for record in item["records"])
    ]
    qualified = [item for item in singleton if item in three_arcs]
    target = [
        item for item in qualified
        if all(record["total"] == record["target"] for record in item["records"])
    ]
    formula_classes = Counter(item["formulas"]["total"] for item in evaluated)
    return {
        "schema": SCHEMA,
        "status": "family_found" if target else "minimal_elbow_island_obstructed",
        "grammar": {
            "state": "(row mod 3, lower-wall mod 3, width in {1,2}, exterior phases, island orientation and alternate phase)",
            "transition": "independent lower/upper advances in {0,1,2,3}; preserve width 1..2; reject a bad seam unit cell",
            "packet": "three transitions with net advance 3 for both walls",
            "raw_nonintersection_wall_cycles": len(wall_packet_cycles()),
            "local_paths": len(paths),
            "width_cap": WIDTH_CAP,
            "phase_rule": "the island uses one of the two phases unequal to its host rail domain",
            "minimality": "width one can change at most one center per packet; width two is the least cap permitting a nonparallel 1<->2 elbow",
        },
        "count_requirement": {
            "one_wall_maximum": "3k^2+6k+2",
            "one_wall_deficit": "k-2",
            "required_island_packet_gain": 1,
            "target": "3k^2+7k",
            "target_stable_gain": "6k+10",
        },
        "classification": {
            "geometry_paths_at_k_7_8_9": len(evaluated),
            "rejections": dict(sorted(rejection.items())),
            "total_formula_classes": dict(sorted(formula_classes.items())),
            "singleton_articulation_paths": len(singleton),
            "stable_three_cap_arc_paths": len(three_arcs),
            "three_arc_singleton_paths": len(qualified),
            "target_paths": len(target),
            "minimum_island_exterior_support_intersection": minimum_intersection,
            "minimum_intersection_example": minimum_example,
        },
        "unconstrained_best": best,
        "three_arc_best": three_arcs[0],
        "obstruction": {
            "local": "every nonempty island meeting the width/phase grammar has at least four island/exterior support vertices",
            "incidence": "the required singleton articulation is absent, including among the stable three-cap-arc paths",
            "capacity": "even after dropping singleton articulation, the best total remains 3k^2+6k+2 and gains only 6k+9",
            "complete_for": "two noncrossing net-three walls, width states 1..2, one alternate row/column island phase, and arbitrary forced-forest perimeter caps",
        },
        "lower_l2_assessment": {
            "blocked_beyond_declared_finite_grammars": False,
            "reason": "the certificate excludes the minimal one-island finite grammar, not wider islands, branching walls, multiple articulations, or nonmonotone domain walls",
            "next_topology": "width at least three with an explicit blank buffer and endpoint-only attachment, or a branching three-wall junction",
        },
        "checks": {
            "all_wall_cycles_nonempty": len(wall_packet_cycles()) == 56,
            "all_evaluated_unit_cells_valid": all(
                r["unit_cells_valid"] for item in evaluated for r in item["records"]
            ),
            "all_evaluated_cores_are_forced_forests": all(
                r["core_forced_forest"] for item in evaluated for r in item["records"]
            ),
            "all_caps_forced_forests": all(r["cap_forced_forest"] for item in evaluated for r in item["records"]),
            "k_7_8_9_complete": all([r["k"] for r in item["records"]] == [7, 8, 9] for item in evaluated),
            "singleton_obstruction": not singleton and minimum_intersection == 4,
            "three_cap_arcs_classified": len(three_arcs) == 56,
            "target_absent": not target,
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
        print(f"elbow/island classification matches {args.output}")
    else:
        args.output.write_text(rendered)
        print(f"wrote {args.output}")


if __name__ == "__main__":
    main()
