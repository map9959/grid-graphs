#!/usr/bin/env python3
"""Exact B20-to-B23 moving-seam pump experiment at surplus one."""

from __future__ import annotations

import argparse
import hashlib
import time
from pathlib import Path

from analysis.transport.census_moving_seam_alignment import find_alignment, replay_alignment
from analysis.patterns.diagonal_patterns import residue_two_affine_pattern
from analysis.searches.search_residue_two_moving_seam import (
    AlignmentState,
    AlignmentTransition,
    ScheduleTemplate,
    build_bidirectional_frontiers,
    join_bidirectional_frontiers,
    result_record,
    write_result,
)
from analysis._paths import ANALYSIS_ROOT


HERE = ANALYSIS_ROOT
SOURCE = HERE / "residue_two_phase_front_witness.txt"
DEFAULT_OUTPUT = HERE / "residue_two_b20_to_b23_result.json"


def load_pattern(path: Path) -> tuple[str, ...]:
    rows = tuple(
        line.strip()
        for line in path.read_text().splitlines()
        if line.strip() and not line.startswith("#")
    )
    if len(rows) != 20 or any(len(row) != 20 or set(row) - {"U", "."} for row in rows):
        raise ValueError("B20 source must be a 20x20 U/. pattern")
    return rows


def fixed_affine_schedule(source: tuple[str, ...], radius: int) -> ScheduleTemplate:
    target = tuple(residue_two_affine_pattern(23))
    alignment = find_alignment(
        source, target, radius, allow_boundary_rewrites=False
    )
    if alignment is None:
        raise ValueError(f"B20 has no strict radius-{radius} alignment to affine n=23")
    replay_alignment(source, target, alignment)
    transitions = []
    cursor = holds = 0
    previous_seam = -1
    for step in alignment.steps:
        before = AlignmentState(cursor, holds, previous_seam)
        cursor += step.operation == "ADVANCE"
        holds += step.operation == "HOLD"
        after = AlignmentState(cursor, holds, step.seam)
        transitions.append(
            AlignmentTransition(
                step.target_row,
                before,
                after,
                step.operation,
                step.source_row,
                step.seam,
            )
        )
        previous_seam = step.seam
    return ScheduleTemplate(
        "b20-to-affine23-lex-first",
        len(source),
        len(target),
        radius,
        tuple(transitions),
    )


def run(
    radius: int, cut: int, output: Path, report: bool, schedule_mode: str
) -> dict:
    source = load_pattern(SOURCE)
    fixed_rows = (*range(6), *range(17, 23))
    schedule = (
        fixed_affine_schedule(source, radius) if schedule_mode == "fixed" else None
    )
    started = time.monotonic()
    frontiers = build_bidirectional_frontiers(
        source=source,
        target_n=23,
        radius=radius,
        u_limit=335,
        cut=cut,
        fixed_rows=fixed_rows,
        schedule=schedule,
        boundary_rewrites=0,
        report=report,
    )
    controls = {}
    for budget in (335, 333):
        controls[str(budget)] = result_record(
            join_bidirectional_frontiers(
                frontiers,
                u_count=budget,
                boundary_rewrites=0,
                bucketed=True,
                use_cache=True,
                report=report,
            )
        )
    record = {
        "schema": "grid-graphs.residue-two-b-state-pump.v1",
        "exact_in_declared_language": True,
        "source": {
            "path": SOURCE.name,
            "n": 20,
            "u_count": sum(row.count("U") for row in source),
            "sha256": hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
            "control_state": "connected unicyclic surplus-one phase-front B20",
        },
        "target_n": 23,
        "radius": radius,
        "cut": cut,
        "fixed_rows": list(fixed_rows),
        "fixed_row_source": "residue_two_affine_pattern(23)",
        "schedule": (
            "lexicographically first strict alignment to affine n=23"
            if schedule is not None
            else "complete monotone alignment automaton with exactly three HOLDs"
        ),
        "schedule_mode": schedule_mode,
        "schedule_steps": (
            [
                {
                    "target_row": edge.target_row,
                    "operation": edge.operation,
                    "source_row": edge.source_row,
                    "source_cursor_before": edge.before.cursor,
                    "seam": edge.seam,
                }
                for edge in schedule.transitions
            ]
            if schedule is not None
            else None
        ),
        "boundary_rewrites": 0,
        "budgets": controls,
        "elapsed_seconds": time.monotonic() - started,
        "scope_note": (
            "This is exact only in the declared moving-seam language and affine cap rows; "
            "a negative result is not a global n=23 impossibility proof."
        ),
    }
    write_result(output, record)
    return record


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--radius", type=int, default=1)
    parser.add_argument("--cut", type=int, default=11)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--schedule", choices=("fixed", "all"), default="fixed")
    parser.add_argument("--quiet", action="store_true")
    args = parser.parse_args()
    if args.radius < 0:
        parser.error("--radius must be non-negative")
    record = run(args.radius, args.cut, args.output, not args.quiet, args.schedule)
    print(
        {
            "output": str(args.output),
            "radius": args.radius,
            "schedule": args.schedule,
            "335": record["budgets"]["335"]["conclusion"],
            "333": record["budgets"]["333"]["conclusion"],
            "elapsed_seconds": record["elapsed_seconds"],
        }
    )


if __name__ == "__main__":
    main()
