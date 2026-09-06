#!/usr/bin/env python3
"""Certify strengthened necessary conditions for the n=17 residue-two target.

For a connected exact-target pattern, every tested condition is necessary: the
target fixes its cardinality, a connected graph has enough edges, every
nontrivial cut is nonempty, and every quotient obtained by contracting vertices
is connected. These tests are not sufficient for connectivity.

The bundled 178-U pattern is intentionally diagnostic.  It passes the old v1
relaxation but fails the strengthened relaxation because bounded face (12,3)
is isolated (face coordinates are zero-based).
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Callable, Hashable

SCHEMA_V1 = "grid-graphs.residue-two-bounded-rank.v1"
SCHEMA_V2 = "grid-graphs.residue-two-necessary-conditions.v2"
LEVELS = ("scalar", "singleton", "interval", "rectangle", "seam", "window")
SEAM_BLOCK_SIZES = (3, 4)
WINDOW_RADIUS = 1

WITNESS = [
    ".U...............",
    ".UUUUUUUUUUUUUUUU",
    ".UUUU.UU.UU.UU.UU",
    ".UU.UUUU.UU.UUUU.",
    ".UU.UU.U.UUUU.UU.",
    ".UU.UU.UUU.UU.UU.",
    ".UU.UU.UUU.UU.UU.",
    ".UU.UUUU.U.UU.UU.",
    ".UU.U.UUUU.UU.UU.",
    ".UUUU.U.UU.UU.UU.",
    ".U.UUUU.UU.UU.UU.",
    ".UUU.UU.UU.UU.UU.",
    ".UUU.UU.UU.UU.UU.",
    ".U...UU.UU.UU.UU.",
    ".UUUUUU.UU.UU.UU.",
    ".UUUUUUUUUUUUUUU.",
    ".U.............U.",
]


def dual_edges(rows: list[str]) -> list[tuple[int, int]]:
    n = len(rows)
    side = n - 1

    def face(row: int, column: int) -> int:
        return 1 + row * side + column

    edges = []
    for row in range(n):
        for column in range(side):
            if rows[row][column] == rows[row][column + 1] == "U":
                edges.append(
                    (
                        0 if row == 0 else face(row - 1, column),
                        0 if row == side else face(row, column),
                    )
                )
    for row in range(side):
        for column in range(n):
            if rows[row][column] == rows[row + 1][column] == "U":
                edges.append(
                    (
                        0 if column == 0 else face(row, column - 1),
                        0 if column == side else face(row, column),
                    )
                )
    return edges


def run_count(lines: list[str]) -> int:
    return sum(
        value == "U" and (index == 0 or line[index - 1] != "U")
        for line in lines
        for index, value in enumerate(line)
    )


def graphic_rank(
    vertices: list[int],
    edges: list[tuple[int, int]],
    quotient: Callable[[int], Hashable],
) -> tuple[int, int, int]:
    quotient_vertices = list(dict.fromkeys(quotient(vertex) for vertex in vertices))
    parent = {vertex: vertex for vertex in quotient_vertices}

    def find(vertex: Hashable) -> Hashable:
        while parent[vertex] != vertex:
            parent[vertex] = parent[parent[vertex]]
            vertex = parent[vertex]
        return vertex

    rank = 0
    for left, right in edges:
        left_root = find(quotient(left))
        right_root = find(quotient(right))
        if left_root != right_root:
            parent[right_root] = left_root
            rank += 1
    components = len({find(vertex) for vertex in quotient_vertices})
    return len(quotient_vertices), rank, components


def validate_pattern(rows: list[str]) -> None:
    n = len(rows)
    if n != 17 or any(len(row) != n or set(row) - {"U", "."} for row in rows):
        raise ValueError("certificate pattern must be a 17x17 array of U and .")


def scalar_measurements(rows: list[str]) -> tuple[dict, list[tuple[int, int]]]:
    validate_pattern(rows)
    n = len(rows)
    side = n - 1
    faces = list(range(1 + side * side))
    edges = dual_edges(rows)
    columns = ["".join(rows[row][column] for row in range(n)) for column in range(n)]
    row_runs = run_count(rows)
    column_runs = run_count(columns)
    u_count = sum(row.count("U") for row in rows)
    edge_count_from_runs = 2 * u_count - row_runs - column_runs
    if edge_count_from_runs != len(edges):
        raise AssertionError("run identity failed")
    full = graphic_rank(faces, edges, lambda vertex: vertex)
    return {
        "n": n,
        "u_count": u_count,
        "dot_count": n * n - u_count,
        "row_runs": row_runs,
        "column_runs": column_runs,
        "run_sum": row_runs + column_runs,
        "dual_edge_count": len(edges),
        "edge_count_from_runs": edge_count_from_runs,
        # This is a diagnostic, not one of the bounded relaxation conditions.
        "full_dual": {"vertices": full[0], "rank": full[1], "components": full[2]},
    }, edges


def cut_size(edges: list[tuple[int, int]], selected: set[int]) -> int:
    return sum((left in selected) != (right in selected) for left, right in edges)


def cut_family_summary(entries: list[tuple[list[int], int]]) -> dict:
    minimum = min(value for _, value in entries)
    return {
        "tested": len(entries),
        "minimum": minimum,
        "minimizers": [descriptor for descriptor, value in entries if value == minimum],
        "violations": [
            {"region": descriptor, "cut_size": value}
            for descriptor, value in entries
            if value < 1
        ],
    }


def singleton_measurements(edges: list[tuple[int, int]], side: int) -> dict:
    values = []
    for row in range(side):
        for column in range(side):
            vertex = 1 + row * side + column
            values.append({"face": [row, column], "cut_size": cut_size(edges, {vertex})})
    return {
        "required_minimum": 1,
        "cuts": values,
        "minimum": min(value["cut_size"] for value in values),
        "violations": [value for value in values if value["cut_size"] < 1],
    }


def interval_measurements(edges: list[tuple[int, int]], side: int) -> dict:
    horizontal = []
    vertical = []
    for fixed in range(side):
        for start in range(side):
            for stop in range(start, side):
                h_vertices = {1 + fixed * side + column for column in range(start, stop + 1)}
                v_vertices = {1 + row * side + fixed for row in range(start, stop + 1)}
                horizontal.append(([fixed, start, stop], cut_size(edges, h_vertices)))
                vertical.append(([fixed, start, stop], cut_size(edges, v_vertices)))
    return {
        "required_minimum": 1,
        "descriptor": {
            "horizontal": ["row", "start_column", "end_column_inclusive"],
            "vertical": ["column", "start_row", "end_row_inclusive"],
        },
        "horizontal": cut_family_summary(horizontal),
        "vertical": cut_family_summary(vertical),
    }


def rectangle_measurements(
    edges: list[tuple[int, int]], side: int, max_rectangle_side: int
) -> dict:
    entries = []
    for height in range(1, max_rectangle_side + 1):
        for width in range(1, max_rectangle_side + 1):
            for top in range(side - height + 1):
                for left in range(side - width + 1):
                    selected = {
                        1 + row * side + column
                        for row in range(top, top + height)
                        for column in range(left, left + width)
                    }
                    entries.append(
                        ([top, left, height, width], cut_size(edges, selected))
                    )
    result = cut_family_summary(entries)
    result.update(
        {
            "required_minimum": 1,
            "max_side": max_rectangle_side,
            "descriptor": ["top_row", "left_column", "height", "width"],
        }
    )
    return result


def rank_record(rank: tuple[int, int, int]) -> dict:
    return {
        "vertices": rank[0],
        "rank": rank[1],
        "required_rank": rank[0] - 1,
        "components": rank[2],
    }


def seam_measurements(edges: list[tuple[int, int]], side: int) -> dict:
    faces = list(range(1 + side * side))
    records = []
    for block_size in SEAM_BLOCK_SIZES:
        for row_offset in range(block_size):
            for column_offset in range(block_size):
                def quotient(
                    vertex: int,
                    b: int = block_size,
                    ro: int = row_offset,
                    co: int = column_offset,
                ) -> tuple:
                    if vertex == 0:
                        return ("exterior",)
                    row, column = divmod(vertex - 1, side)
                    if (row - ro) % b == 0 or (column - co) % b == 0:
                        return ("seam-face", row, column)
                    return ("block", (row - ro) // b, (column - co) // b)

                record = {
                    "block_size": block_size,
                    "row_offset": row_offset,
                    "column_offset": column_offset,
                }
                record.update(rank_record(graphic_rank(faces, edges, quotient)))
                records.append(record)
    return {
        "construction": (
            "keep offset seam rows and columns as singleton faces; contract each "
            "remaining open block between seams; keep exterior separate"
        ),
        "records": records,
        "violations": [record for record in records if record["rank"] != record["required_rank"]],
    }


def window_measurements(edges: list[tuple[int, int]], side: int) -> dict:
    faces = list(range(1 + side * side))
    records = []
    for center_row in range(side):
        for center_column in range(side):
            inside = {
                1 + row * side + column
                for row in range(max(0, center_row - WINDOW_RADIUS), min(side, center_row + WINDOW_RADIUS + 1))
                for column in range(max(0, center_column - WINDOW_RADIUS), min(side, center_column + WINDOW_RADIUS + 1))
            }

            def quotient(vertex: int) -> tuple:
                return ("face", vertex) if vertex in inside else ("contracted_exterior",)

            record = {"center": [center_row, center_column]}
            record.update(rank_record(graphic_rank(faces, edges, quotient)))
            records.append(record)
    return {
        "radius": WINDOW_RADIUS,
        "metric": "Chebyshev",
        "construction": "keep bounded faces in the clipped window separate; contract every other vertex",
        "records": records,
        "violations": [record for record in records if record["rank"] != record["required_rank"]],
    }


def family_configuration(level: str, max_rectangle_side: int) -> dict:
    included = list(LEVELS[: LEVELS.index(level) + 1])
    return {
        "level": level,
        "included": included,
        "face_coordinates": "zero-based [row,column] on the 16x16 bounded-face grid",
        "cut_threshold": 1,
        "rectangle": {
            "max_side": max_rectangle_side,
            "regions": "proper nonempty bounded-face rectangles",
        },
        "seam": {"block_sizes": list(SEAM_BLOCK_SIZES), "offsets": "all b^2 offsets"},
        "window": {"radius": WINDOW_RADIUS, "metric": "Chebyshev"},
    }


def relaxation_violations(measurements: dict, level: str) -> list[str]:
    failures = []
    if measurements["u_count"] != 178:
        failures.append(f"U count is {measurements['u_count']}, required 178")
    if measurements["dot_count"] != 111:
        failures.append(f"dot count is {measurements['dot_count']}, required 111")
    if measurements["run_sum"] > 100:
        failures.append(f"run sum is {measurements['run_sum']}, maximum 100")
    if measurements["dual_edge_count"] < 256:
        failures.append(f"dual edge count is {measurements['dual_edge_count']}, minimum 256")
    if LEVELS.index(level) >= LEVELS.index("singleton"):
        for violation in measurements["singleton_cuts"]["violations"]:
            row, column = violation["face"]
            failures.append(
                f"isolated face ({row},{column}): singleton cut size {violation['cut_size']}"
            )
    if LEVELS.index(level) >= LEVELS.index("interval"):
        for orientation in ("horizontal", "vertical"):
            for violation in measurements["interval_cuts"][orientation]["violations"]:
                failures.append(
                    f"{orientation} interval {violation['region']} has cut size {violation['cut_size']}"
                )
    if LEVELS.index(level) >= LEVELS.index("rectangle"):
        for violation in measurements["rectangle_cuts"]["violations"]:
            failures.append(
                f"rectangle {violation['region']} has cut size {violation['cut_size']}"
            )
    if LEVELS.index(level) >= LEVELS.index("seam"):
        for violation in measurements["seam_quotients"]["violations"]:
            failures.append(
                "seam quotient "
                f"b={violation['block_size']} offset=({violation['row_offset']},"
                f"{violation['column_offset']}) rank {violation['rank']}/"
                f"{violation['required_rank']}"
            )
    if LEVELS.index(level) >= LEVELS.index("window"):
        for violation in measurements["window_quotients"]["violations"]:
            failures.append(
                f"window centered at {violation['center']} rank {violation['rank']}/"
                f"{violation['required_rank']}"
            )
    return failures


def make_certificate(
    rows: list[str], level: str = "window", max_rectangle_side: int = 4
) -> dict:
    if level not in LEVELS:
        raise ValueError(f"level must be one of {','.join(LEVELS)}")
    if not 1 <= max_rectangle_side <= 16:
        raise ValueError("maximum rectangle side must lie in 1..16")
    result, edges = scalar_measurements(rows)
    side = len(rows) - 1
    included = LEVELS[: LEVELS.index(level) + 1]
    if "singleton" in included:
        result["singleton_cuts"] = singleton_measurements(edges, side)
    if "interval" in included:
        result["interval_cuts"] = interval_measurements(edges, side)
    if "rectangle" in included:
        result["rectangle_cuts"] = rectangle_measurements(edges, side, max_rectangle_side)
    if "seam" in included:
        result["seam_quotients"] = seam_measurements(edges, side)
    if "window" in included:
        result["window_quotients"] = window_measurements(edges, side)
    failures = relaxation_violations(result, level)
    return {
        "schema": SCHEMA_V2,
        "relaxation": {
            "n": 17,
            "u_count": 178,
            "maximum_run_sum": 100,
            "minimum_dual_edges": 256,
            "families": family_configuration(level, max_rectangle_side),
        },
        "pattern": rows,
        "measurements": result,
        "relaxation_feasible": not failures,
        "global_dual_connected": result["full_dual"]["components"] == 1,
    }


# v1 is retained only so previously emitted JSON can still be recomputed exactly.
def measurements(rows: list[str], block_size: int) -> dict:
    result, edges = scalar_measurements(rows)
    if not 1 <= block_size <= 16:
        raise ValueError("block size must lie in 1..16")
    side = len(rows) - 1
    faces = list(range(1 + side * side))

    def coordinates(vertex: int) -> tuple[int, int]:
        return divmod(vertex - 1, side)

    def row_quotient(vertex: int) -> tuple[str, int]:
        return ("out", 0) if vertex == 0 else ("row", coordinates(vertex)[0])

    def column_quotient(vertex: int) -> tuple[str, int]:
        return ("out", 0) if vertex == 0 else ("column", coordinates(vertex)[1])

    def block_quotient(vertex: int) -> tuple:
        if vertex == 0:
            return ("out",)
        row, column = coordinates(vertex)
        return ("block", row // block_size, column // block_size)

    row_rank = graphic_rank(faces, edges, row_quotient)
    column_rank = graphic_rank(faces, edges, column_quotient)
    block_rank = graphic_rank(faces, edges, block_quotient)
    result["row_quotient"] = rank_record(row_rank)
    result["column_quotient"] = rank_record(column_rank)
    result["block_quotient"] = {
        "block_size": block_size,
        "vertices": block_rank[0],
        "rank": block_rank[1],
        "components": block_rank[2],
    }
    # v1 did not contain the explicit required_rank fields.
    del result["row_quotient"]["required_rank"]
    del result["column_quotient"]["required_rank"]
    return result


def relaxation_feasible(result: dict) -> bool:
    quotients = ("row_quotient", "column_quotient", "block_quotient")
    return (
        result["u_count"] == 178
        and result["dot_count"] == 111
        and result["run_sum"] <= 100
        and result["dual_edge_count"] >= 256
        and all(result[name]["rank"] == result[name]["vertices"] - 1 for name in quotients)
    )


def make_v1_certificate(rows: list[str], block_size: int) -> dict:
    result = measurements(rows, block_size)
    return {
        "schema": SCHEMA_V1,
        "relaxation": {
            "n": 17,
            "u_count": 178,
            "maximum_run_sum": 100,
            "minimum_dual_edges": 256,
            "contractions": ["face_rows", "face_columns", f"aligned_{block_size}x{block_size}_blocks"],
        },
        "block_size": block_size,
        "pattern": rows,
        "measurements": result,
        "relaxation_feasible": relaxation_feasible(result),
        "global_dual_connected": result["full_dual"]["components"] == 1,
    }


def same_json_value(left, right) -> bool:
    if type(left) is not type(right):
        return False
    if isinstance(left, dict):
        return left.keys() == right.keys() and all(
            same_json_value(left[key], right[key]) for key in left
        )
    if isinstance(left, list):
        return len(left) == len(right) and all(
            same_json_value(a, b) for a, b in zip(left, right)
        )
    return left == right


def verify(certificate: dict, allow_infeasible: bool = False) -> None:
    if not isinstance(certificate, dict):
        raise TypeError("certificate must be a JSON object")
    schema = certificate.get("schema")
    if schema == SCHEMA_V1:
        rebuilt = make_v1_certificate(certificate["pattern"], certificate["block_size"])
    elif schema == SCHEMA_V2:
        families = certificate["relaxation"]["families"]
        rebuilt = make_certificate(
            certificate["pattern"], families["level"], families["rectangle"]["max_side"]
        )
    else:
        raise ValueError("unknown certificate schema")
    if not same_json_value(rebuilt, certificate):
        raise ValueError("certificate fields do not match complete recomputation")
    if not rebuilt["relaxation_feasible"] and not allow_infeasible:
        raise ValueError("pattern fails the stated relaxation (use --allow-infeasible for diagnostics)")


def failure_report(certificate: dict) -> str:
    families = certificate["relaxation"]["families"]
    failures = relaxation_violations(certificate["measurements"], families["level"])
    return "FAILED strengthened relaxation:\n" + "\n".join(f"  - {failure}" for failure in failures)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--level", choices=LEVELS, default="window")
    parser.add_argument("--max-rectangle-side", type=int, default=4)
    parser.add_argument("--output", type=Path, help="write the JSON certificate")
    parser.add_argument("--verify", type=Path, help="completely recompute a JSON certificate")
    parser.add_argument("--json", action="store_true", help="print the complete certificate")
    parser.add_argument(
        "--allow-infeasible",
        action="store_true",
        help="write or verify a diagnostic certificate that fails its relaxation",
    )
    args = parser.parse_args()

    if args.verify:
        certificate = json.loads(args.verify.read_text())
        try:
            verify(certificate, allow_infeasible=args.allow_infeasible)
        except (AttributeError, KeyError, TypeError, ValueError) as error:
            raise SystemExit(f"INVALID relaxation certificate: {error}") from error
        result = certificate["measurements"]
        if certificate["schema"] == SCHEMA_V2 and not certificate["relaxation_feasible"]:
            print("VERIFIED diagnostic certificate by complete recomputation")
            print(failure_report(certificate))
        else:
            print(
                f"VALID relaxation certificate: U={result['u_count']} dots={result['dot_count']} "
                f"runs={result['run_sum']} edges={result['dual_edge_count']}"
            )
        return

    try:
        certificate = make_certificate(WITNESS, args.level, args.max_rectangle_side)
    except ValueError as error:
        raise SystemExit(str(error)) from error
    if not certificate["relaxation_feasible"] and not args.allow_infeasible:
        raise SystemExit(failure_report(certificate))
    verify(certificate, allow_infeasible=args.allow_infeasible)
    if args.output:
        args.output.write_text(json.dumps(certificate, indent=2) + "\n")
    if args.json:
        print(json.dumps(certificate, indent=2))
        return

    result = certificate["measurements"]
    status = "FEASIBLE" if certificate["relaxation_feasible"] else "DIAGNOSTIC INFEASIBLE"
    print(
        f"{status} v2 relaxation at level {args.level}: U={result['u_count']} "
        f"dots={result['dot_count']} runs={result['row_runs']}+{result['column_runs']}="
        f"{result['run_sum']} edges={result['dual_edge_count']}"
    )
    if not certificate["relaxation_feasible"]:
        print(failure_report(certificate))
    print(
        f"global diagnostic: full dual rank={result['full_dual']['rank']}/256 "
        f"components={result['full_dual']['components']}"
    )
    if args.output:
        print(f"certificate: {args.output}")


if __name__ == "__main__":
    main()
