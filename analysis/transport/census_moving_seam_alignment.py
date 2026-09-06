#!/usr/bin/env python3
"""Census asynchronous moving-seam alignments between residue-two patterns.

For n=3k+2, a row is represented by its two boundary cells and k packets of
three cells.  A target row has k+1 packets.  Deleting one target packet aligns
the remaining packets with a source row.  Aligned packets outside the requested
radius from the deleted packet match exactly.  Boundary cells are controlled by
a separate strict-or-rewrite policy and never belong to the packet tube.

An ADVANCE row compares with and consumes the source row at the cursor.  A
HOLD row is available only after an ADVANCE and compares with cursor-1 without
moving the cursor.  Thus target-to-source correspondence is a monotone
surjection.  A complete path uses exactly three HOLD rows, consumes both
patterns, and moves its seam by at most one packet between emitted target rows.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path

from analysis._paths import analysis_path
from analysis.patterns.diagonal_patterns import (
    residue_two_affine_pattern,
    residue_two_pattern,
)
from analysis.patterns.dual_decycling import parse_pattern

SCHEMA = "grid-graphs.d4-moving-seam-alignment-census.v2"
PHASE_FRONT_WITNESS = analysis_path("residue_two_phase_front_witness.txt")


@dataclass(frozen=True, slots=True)
class Orientation:
    name: str
    aliases: tuple[str, ...]
    rows: tuple[str, ...]


@dataclass(frozen=True, slots=True)
class RowCensus:
    inserted_u: int
    inserted_dot: int
    aligned_rewrites: int
    rewrites_to_u: int
    rewrites_to_dot: int
    boundary_rewrites: int
    boundary_rewrites_to_u: int
    boundary_rewrites_to_dot: int
    exterior_cells: int


@dataclass(frozen=True, slots=True)
class Step:
    target_row: int
    operation: str
    source_row: int
    source_cursor_before: int
    seam: int
    row_census: RowCensus


@dataclass(frozen=True, slots=True)
class Alignment:
    radius: int
    allow_boundary_rewrites: bool
    source_orientation: str
    target_orientation: str
    steps: tuple[Step, ...]


def load_square_pattern(path: Path) -> list[str]:
    """Parse a raw or annotated U-pattern and validate it as a square."""
    try:
        rows = parse_pattern(path.read_text())
    except SystemExit as error:
        raise ValueError(f"{path} does not contain a U-pattern") from error
    if not rows or any(len(row) != len(rows) for row in rows):
        raise ValueError(f"{path} does not contain a square pattern")
    if any(set(row) - {".", "U"} for row in rows):
        raise ValueError(f"{path} contains cells other than '.' and 'U'")
    return rows


def _rotate_90(rows: tuple[str, ...]) -> tuple[str, ...]:
    n = len(rows)
    return tuple("".join(rows[n - 1 - row][column] for row in range(n)) for column in range(n))


def d4_orientations(rows: list[str] | tuple[str, ...]) -> tuple[Orientation, ...]:
    """Return D4 images in action order, combining actions with equal images."""
    original = tuple(rows)
    if not original or any(len(row) != len(original) for row in original):
        raise ValueError("D4 transforms require a square pattern")
    rotations = [original]
    for _ in range(3):
        rotations.append(_rotate_90(rotations[-1]))
    named = []
    for index, transformed in enumerate(rotations):
        named.append((f"rotate_{90 * index}", transformed))
    for index, transformed in enumerate(rotations):
        named.append((f"rotate_{90 * index}_reflect_lr", tuple(row[::-1] for row in transformed)))

    unique: dict[tuple[str, ...], list[str]] = {}
    for name, transformed in named:
        unique.setdefault(transformed, []).append(name)
    return tuple(
        Orientation(names[0], tuple(names), transformed)
        for transformed, names in unique.items()
    )


def row_alignment_census(
    source: str,
    target: str,
    seam: int,
    radius: int,
    *,
    allow_boundary_rewrites: bool = False,
) -> RowCensus | None:
    """Return counts if deleting ``seam`` makes two rows compatible.

    The inserted packet is always arbitrary.  Radius applies only to aligned
    packets; boundary mismatches require ``allow_boundary_rewrites`` and are
    counted in their own channel.
    """
    if len(target) != len(source) + 3 or (len(source) - 2) % 3:
        raise ValueError("rows must have widths 3k+2 and 3(k+1)+2")
    packet_count = (len(source) - 2) // 3
    if seam not in range(packet_count + 1) or radius < 0:
        raise ValueError("invalid seam or radius")
    boundary_pairs = ((source[0], target[0]), (source[-1], target[-1]))
    if not allow_boundary_rewrites and any(a != b for a, b in boundary_pairs):
        return None
    boundary_rewrites_to_u = sum(a != b and b == "U" for a, b in boundary_pairs)
    boundary_rewrites_to_dot = sum(a != b and b == "." for a, b in boundary_pairs)

    inserted = target[1 + 3 * seam : 1 + 3 * (seam + 1)]
    rewrites_to_u = 0
    rewrites_to_dot = 0
    exterior_cells = 2
    for target_packet in range(packet_count + 1):
        if target_packet == seam:
            continue
        source_packet = target_packet if target_packet < seam else target_packet - 1
        source_cells = source[1 + 3 * source_packet : 1 + 3 * (source_packet + 1)]
        target_cells = target[1 + 3 * target_packet : 1 + 3 * (target_packet + 1)]
        in_tube = abs(target_packet - seam) <= radius
        if not in_tube:
            exterior_cells += 3
            if source_cells != target_cells:
                return None
            continue
        for source_cell, target_cell in zip(source_cells, target_cells, strict=True):
            if source_cell != target_cell:
                if target_cell == "U":
                    rewrites_to_u += 1
                else:
                    rewrites_to_dot += 1
    return RowCensus(
        inserted.count("U"),
        inserted.count("."),
        rewrites_to_u + rewrites_to_dot,
        rewrites_to_u,
        rewrites_to_dot,
        boundary_rewrites_to_u + boundary_rewrites_to_dot,
        boundary_rewrites_to_u,
        boundary_rewrites_to_dot,
        exterior_cells,
    )


def _transition_kinds(cursor: int, source_size: int) -> tuple[tuple[str, int, int], ...]:
    transitions = []
    if cursor < source_size:
        transitions.append(("ADVANCE", cursor, cursor + 1))
    if cursor > 0:
        transitions.append(("HOLD", cursor - 1, cursor))
    return tuple(transitions)


def find_alignment(
    source: list[str] | tuple[str, ...],
    target: list[str] | tuple[str, ...],
    radius: int,
    *,
    allow_boundary_rewrites: bool = False,
    source_orientation: str = "rotate_0",
    target_orientation: str = "rotate_0",
) -> Alignment | None:
    """Find the lexicographically first complete alignment by dynamic programming."""
    source = tuple(source)
    target = tuple(target)
    if len(target) != len(source) + 3 or any(len(row) != len(source) for row in source):
        raise ValueError("source must be n by n and target must have n+3 rows")
    if any(len(row) != len(target) for row in target):
        raise ValueError("target must be square")
    if len(target) - len(source) != 3:
        raise ValueError("target size must be source size plus three")
    packet_count = (len(target) - 2) // 3

    # State is (source cursor, HOLD count, previous seam).  Insertion order is
    # the tie-break: ADVANCE, HOLD, then lower seam and first DP parent.
    states: dict[tuple[int, int, int], tuple[Step, ...]] = {}
    for target_row, target_cells in enumerate(target):
        children: dict[tuple[int, int, int], tuple[Step, ...]] = {}
        parents = states.items() if target_row else [((0, 0, -1), ())]
        for (cursor, holds, previous_seam), path in parents:
            for operation, source_row, next_cursor in _transition_kinds(cursor, len(source)):
                next_holds = holds + (operation == "HOLD")
                if next_holds > 3:
                    continue
                seams = range(packet_count) if previous_seam < 0 else range(
                    max(0, previous_seam - 1), min(packet_count, previous_seam + 2)
                )
                for seam in seams:
                    census = row_alignment_census(
                        source[source_row],
                        target_cells,
                        seam,
                        radius,
                        allow_boundary_rewrites=allow_boundary_rewrites,
                    )
                    if census is None:
                        continue
                    key = (next_cursor, next_holds, seam)
                    if key not in children:
                        children[key] = path + (
                            Step(
                                target_row,
                                operation,
                                source_row,
                                cursor,
                                seam,
                                census,
                            ),
                        )
        states = children
        if not states:
            return None

    candidates = [
        path for (cursor, holds, _), path in states.items()
        if cursor == len(source) and holds == 3
    ]
    if not candidates:
        return None
    return Alignment(
        radius,
        allow_boundary_rewrites,
        source_orientation,
        target_orientation,
        candidates[0],
    )


def replay_alignment(
    source: list[str] | tuple[str, ...],
    target: list[str] | tuple[str, ...],
    alignment: Alignment,
) -> dict[str, int]:
    """Validate a reconstructed path and return its aggregate rewrite census."""
    cursor = 0
    holds = 0
    previous_seam: int | None = None
    totals = {field: 0 for field in RowCensus.__dataclass_fields__}
    if len(alignment.steps) != len(target):
        raise ValueError("path does not emit every target row")
    for target_row, step in enumerate(alignment.steps):
        if step.target_row != target_row or step.source_cursor_before != cursor:
            raise ValueError("path row or source cursor is inconsistent")
        choices = _transition_kinds(cursor, len(source))
        choice = next(
            (item for item in choices if item[:2] == (step.operation, step.source_row)),
            None,
        )
        if choice is None:
            raise ValueError("path operation is unavailable at its source cursor")
        if previous_seam is not None and abs(step.seam - previous_seam) > 1:
            raise ValueError("seam moves by more than one packet")
        census = row_alignment_census(
            source[step.source_row],
            target[target_row],
            step.seam,
            alignment.radius,
            allow_boundary_rewrites=alignment.allow_boundary_rewrites,
        )
        if census is None or census != step.row_census:
            raise ValueError("path row is incompatible or has an incorrect census")
        for field in totals:
            totals[field] += getattr(census, field)
        cursor = choice[2]
        holds += step.operation == "HOLD"
        previous_seam = step.seam
    if cursor != len(source) or holds != 3:
        raise ValueError("path does not consume the source with exactly three HOLDs")
    return totals


def _alignment_json(alignment: Alignment) -> dict:
    data = asdict(alignment)
    data["hold_rows"] = [
        {"target_row": step.target_row, "source_row": step.source_row}
        for step in alignment.steps if step.operation == "HOLD"
    ]
    data["seam_schedule"] = [step.seam for step in alignment.steps]
    return data


def census_pair(
    label: str,
    source: list[str],
    target: list[str],
    max_radius: int | None = None,
    *,
    allow_boundary_rewrites: bool = True,
) -> dict:
    source_orientations = d4_orientations(source)
    target_orientations = d4_orientations(target)
    packet_count = (len(target) - 2) // 3
    if max_radius is None:
        max_radius = packet_count
    radii = []
    minimum = None
    for radius in range(max_radius + 1):
        match = None
        for source_orientation in source_orientations:
            for target_orientation in target_orientations:
                match = find_alignment(
                    source_orientation.rows,
                    target_orientation.rows,
                    radius,
                    allow_boundary_rewrites=allow_boundary_rewrites,
                    source_orientation=source_orientation.name,
                    target_orientation=target_orientation.name,
                )
                if match is not None:
                    break
            if match is not None:
                break
        radius_record = {"radius": radius, "works": match is not None, "alignment": None}
        if match is not None:
            radius_record["alignment"] = _alignment_json(match)
            radius_record["alignment"]["rewrite_census"] = replay_alignment(
                next(item.rows for item in source_orientations if item.name == match.source_orientation),
                next(item.rows for item in target_orientations if item.name == match.target_orientation),
                match,
            )
            if minimum is None:
                minimum = radius
        radii.append(radius_record)
    return {
        "label": label,
        "source": {"n": len(source), "u_cells": sum(row.count("U") for row in source)},
        "target": {"n": len(target), "u_cells": sum(row.count("U") for row in target)},
        "allow_boundary_rewrites": allow_boundary_rewrites,
        "source_orientations": [
            {"name": item.name, "aliases": list(item.aliases)} for item in source_orientations
        ],
        "target_orientations": [
            {"name": item.name, "aliases": list(item.aliases)} for item in target_orientations
        ],
        "minimum_radius": minimum,
        "radii": radii,
    }


def census_known_pairs(max_radius: int | None = None) -> dict:
    pairs = (
        ("exact-8-to-exact-11", residue_two_pattern(8), residue_two_pattern(11)),
        ("exact-11-to-exact-14", residue_two_pattern(11), residue_two_pattern(14)),
        ("exact-14-to-affine-17", residue_two_pattern(14), residue_two_affine_pattern(17)),
        (
            "affine-17-to-phase-front-20",
            residue_two_affine_pattern(17),
            load_square_pattern(PHASE_FRONT_WITNESS),
        ),
    )
    return {
        "schema": SCHEMA,
        "semantics": {
            "packet_width": 3,
            "known_pair_boundary_policy": "permit and count rewrites separately from packet radius",
            "strict_boundary_policy_available": True,
            "radius": (
                "the inserted seam packet is arbitrary; aligned target packets q with "
                "abs(q-seam) <= radius are arbitrary; boundaries are separate"
            ),
            "advance": "compare target row to source cursor, then consume source row",
            "hold": "only when cursor>0, compare target row to source cursor-1 without consuming",
            "correspondence": "monotone surjection from target rows onto source rows",
            "required_holds": 3,
            "required_advances": "source n",
            "maximum_seam_step": 1,
            "interpretation": "similarity census only; large radius is not topology evidence",
            "tie_break": "D4 action order; ADVANCE before HOLD; lower seam; first DP parent",
        },
        "pairs": [census_pair(label, source, target, max_radius) for label, source, target in pairs],
    }


def _human_report(record: dict) -> str:
    lines = []
    for pair in record["pairs"]:
        outcomes = ", ".join(
            f"r={item['radius']}:{'yes' if item['works'] else 'no'}" for item in pair["radii"]
        )
        lines.append(
            f"{pair['label']} ({pair['source']['u_cells']} U -> {pair['target']['u_cells']} U): "
            f"{outcomes}; minimum={pair['minimum_radius']}"
        )
        match = next((item["alignment"] for item in pair["radii"] if item["works"]), None)
        if match:
            holds = ", ".join(
                f"{item['target_row']}->source {item['source_row']}" for item in match["hold_rows"]
            )
            lines.append(
                f"  D4={match['source_orientation']}->{match['target_orientation']}; "
                f"HOLDs={holds}; seams={match['seam_schedule']}; rewrites={match['rewrite_census']}"
            )
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", help="print the reproducible JSON census")
    parser.add_argument("--max-radius", type=int, help="largest packet radius to test")
    args = parser.parse_args()
    record = census_known_pairs(args.max_radius)
    if args.json:
        print(json.dumps(record, indent=2, sort_keys=True))
    else:
        print(_human_report(record))


if __name__ == "__main__":
    main()
