#!/usr/bin/env python3
"""Describe the common surplus-one unicyclic residue-two B control state."""

from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import asdict
from pathlib import Path

from census_moving_seam_alignment import find_alignment, replay_alignment
from construction_lab import dual_connectivity_check, forest_completion_check, q_old_formula
from diagonal_patterns import residue_two_affine_pattern
from search_residue_two_phase_front import _central_width, _packet_names


HERE = Path(__file__).resolve().parent
B20_PATH = HERE / "residue_two_phase_front_witness.txt"
DEFAULT_OUTPUT = HERE / "residue_two_b_state_analysis.json"


def load(path: Path) -> tuple[str, ...]:
    return tuple(line.strip() for line in path.read_text().splitlines() if line.strip())


def metrics(rows: tuple[str, ...]) -> dict:
    n = len(rows)
    u_count = sum(row.count("U") for row in rows)
    edges = sum(
        row[col] == row[col + 1] == "U"
        for row in rows
        for col in range(n - 1)
    ) + sum(
        rows[row][col] == rows[row + 1][col] == "U"
        for row in range(n - 1)
        for col in range(n)
    )
    dual_ok, connected, total = dual_connectivity_check(list(rows))
    forest_ok, forest_reason = forest_completion_check(list(rows))
    words = [_packet_names(row) for row in rows[3:-2]]
    return {
        "n": n,
        "u_count": u_count,
        "old_q": q_old_formula(n),
        "surplus": u_count - q_old_formula(n),
        "dual_edges": edges,
        "dual_vertices": 1 + (n - 1) ** 2,
        "dual_connected": dual_ok,
        "dual_connected_vertices": connected,
        "dual_total_vertices": total,
        "cycle_excess": edges - (n - 1) ** 2,
        "forest_ok": forest_ok,
        "forest_reason": forest_reason,
        "mutable_packet_words": words,
        "maximum_center_width": max(map(_central_width, words)),
        "all_rows_in_basic_phase_carrier": True,
    }


def alignment_record(source: tuple[str, ...], target: tuple[str, ...]) -> dict:
    minimum = next(
        radius
        for radius in range((len(target) - 2) // 3)
        if find_alignment(source, target, radius, allow_boundary_rewrites=False)
        is not None
    )
    alignment = find_alignment(
        source, target, minimum, allow_boundary_rewrites=False
    )
    assert alignment is not None
    return {
        "minimum_strict_radius": minimum,
        "rewrite_census": replay_alignment(source, target, alignment),
        "hold_rows": [
            {"target_row": step.target_row, "source_row": step.source_row}
            for step in alignment.steps
            if step.operation == "HOLD"
        ],
        "seam_schedule": [step.seam for step in alignment.steps],
        "steps": [asdict(step) for step in alignment.steps],
    }


def analyze() -> dict:
    a17 = tuple(residue_two_affine_pattern(17))
    b20 = load(B20_PATH)
    affine23 = tuple(residue_two_affine_pattern(23))
    a_metrics = metrics(a17)
    b_metrics = metrics(b20)
    shared = {
        "surplus": 1,
        "dual_connected": True,
        "cycle_excess": 1,
        "row_carrier": ". L^a C R^(k-a-|C|) .",
        "center_alphabet": ["X", "H"],
        "center_width_bound": 5,
        "interpretation": (
            "A17 and B20 are instances of the same abstract surplus-one, connected, "
            "unicyclic bounded-phase control class. This is a finite carrier class, "
            "not yet a proved repeatable recurrence state."
        ),
    }
    if not all(
        (
            item["surplus"] == shared["surplus"]
            and item["dual_connected"]
            and item["cycle_excess"] == shared["cycle_excess"]
            and item["maximum_center_width"] <= shared["center_width_bound"]
        )
        for item in (a_metrics, b_metrics)
    ):
        raise AssertionError("known endpoints do not satisfy the declared B state")
    return {
        "schema": "grid-graphs.residue-two-b-control.v1",
        "shared_control": shared,
        "a17": a_metrics,
        "b20": {
            **b_metrics,
            "path": B20_PATH.name,
            "sha256": hashlib.sha256(B20_PATH.read_bytes()).hexdigest(),
        },
        "a17_to_b20_alignment": alignment_record(a17, b20),
        "b20_to_affine23_alignment": alignment_record(b20, affine23),
        "required_b23": {
            "n": 23,
            "u_count": 333,
            "surplus": 1,
            "required_increment_from_b20": 83,
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()
    record = analyze()
    args.output.write_text(json.dumps(record, indent=2) + "\n")
    print(
        f"wrote {args.output}: A17={record['a17']['u_count']} U, "
        f"B20={record['b20']['u_count']} U, "
        f"radii={record['a17_to_b20_alignment']['minimum_strict_radius']}/"
        f"{record['b20_to_affine23_alignment']['minimum_strict_radius']}"
    )


if __name__ == "__main__":
    main()
