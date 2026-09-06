#!/usr/bin/env python3
"""Exact bounded enlargement at the n=23 recurrence attachment cut.

This language strictly contains the A5_H3_A15 and A8_H3_A12 basic families.
Only target rows 5 and 20, where their common best joins expose a one-cell
attachment cut, gain a full binary radius-two packet window.  All other rows,
row charges, and the five declared affine cap rows remain fixed as before.
"""

from __future__ import annotations

import argparse
import itertools
import json
import time
from dataclasses import asdict
from functools import cache
from pathlib import Path

from analysis._paths import ANALYSIS_ROOT
from analysis.patterns.construction_lab import run_check
from analysis.patterns.diagonal_patterns import residue_two_affine_pattern
from analysis.searches.search_residue_two_b_state_phase_pump import (
    cost_bounds,
    expand_side,
    join,
)
from analysis.searches.search_residue_two_b_state_pump import SOURCE, load_pattern
from analysis.searches.search_residue_two_target_recurrence import (
    CAP_ROWS,
    PACKETS,
    SCHEDULES,
    TARGET_U,
    N,
    hold_rows,
    rows_sha256,
    widened_rows,
)
from analysis.tiles.tile_grammar import render_mask, row_mask

HERE = ANALYSIS_ROOT
DEFAULT_OUTPUT = HERE / "residue_two_n23_target_recurrence_attachment_result.json"
DEFAULT_WITNESS = HERE / "residue_two_n23_target_recurrence_attachment_witness.txt"
SCHEMA = "grid-graphs.residue-two-target-recurrence-attachment.v1"
ATTACHMENT_ROWS = (5, 20)
ATTACHMENT_PACKETS = (4, 5)
REWRITE_RADIUS = 2
REWRITE_PACKETS = tuple(
    packet
    for packet in range(PACKETS)
    if min(abs(packet - cut) for cut in ATTACHMENT_PACKETS) <= REWRITE_RADIUS
)
FULL_BINARY_PACKETS = tuple(
    "".join("U" if bit else "." for bit in bits)
    for bits in itertools.product((False, True), repeat=3)
)
PHASES = {
    "main_diagonal": ("main_diagonal", "main_diagonal", "main_diagonal"),
    "anti_diagonal": ("anti_diagonal", "anti_diagonal", "anti_diagonal"),
    "main_with_anti_bottom_cap": ("main_diagonal", "main_diagonal", "anti_diagonal"),
    "anti_with_main_bottom_cap": ("anti_diagonal", "anti_diagonal", "main_diagonal"),
}


def orient_row(row: str, phase: str) -> str:
    if phase == "main_diagonal":
        return row
    if phase == "anti_diagonal":
        return row[::-1]
    raise ValueError(f"unknown row phase {phase}")


@cache
def attachment_rewrites(rows: tuple[str, ...]) -> tuple[int, ...]:
    """Add every exact-charge binary filling of the declared packet window."""
    masks = {row_mask(row) for row in rows}
    for row in rows:
        target_charge = row.count("U")
        packets = [row[1 + 3 * packet : 4 + 3 * packet] for packet in range(PACKETS)]
        fixed_charge = sum(
            packet.count("U")
            for index, packet in enumerate(packets)
            if index not in REWRITE_PACKETS
        )
        needed = target_charge - fixed_charge
        for replacement in itertools.product(FULL_BINARY_PACKETS, repeat=len(REWRITE_PACKETS)):
            if sum(packet.count("U") for packet in replacement) != needed:
                continue
            candidate = packets.copy()
            for index, packet in zip(REWRITE_PACKETS, replacement, strict=True):
                candidate[index] = packet
            masks.add(row_mask("." + "".join(candidate) + "."))
    return tuple(sorted(masks))


def schedule_domains(schedule: str, phase: str) -> tuple[tuple[int, ...], ...]:
    try:
        operations = SCHEDULES[schedule]
        body_phase, top_cap_phase, bottom_cap_phase = PHASES[phase]
    except KeyError as error:
        raise ValueError(f"unknown schedule or phase: {schedule}/{phase}") from error

    source = load_pattern(SOURCE)
    cap = residue_two_affine_pattern(N)
    domains = []
    cursor = 0
    for target_row, operation in enumerate(operations):
        if target_row in CAP_ROWS:
            cap_phase = top_cap_phase if target_row <= 2 else bottom_cap_phase
            masks = (row_mask(orient_row(cap[target_row], cap_phase)),)
        else:
            if operation == "A":
                if not 3 <= cursor <= 17:
                    raise AssertionError("ADVANCE row mapped outside B20 mutable rows")
                basic_rows = widened_rows(source[cursor])
            else:
                basic_rows = hold_rows()
            if target_row in ATTACHMENT_ROWS:
                main_masks = attachment_rewrites(basic_rows)
            else:
                main_masks = tuple(sorted({row_mask(row) for row in basic_rows}))
            if body_phase == "anti_diagonal":
                masks = tuple(
                    sorted(
                        row_mask(orient_row(render_mask(mask, N), body_phase))
                        for mask in main_masks
                    )
                )
            else:
                masks = main_masks
        domains.append(masks)
        if operation == "A":
            cursor += 1

    if cursor != 20:
        raise AssertionError("schedule does not consume all twenty source rows")
    if any(len({mask.bit_count() for mask in domain}) != 1 for domain in domains):
        raise AssertionError("a row domain mixes charges")
    if sum(domain[0].bit_count() for domain in domains) != TARGET_U:
        raise AssertionError("declared domains are not fixed at 333 U")
    return tuple(domains)


def run_family(schedule: str, phase: str, cut: int, report: bool) -> dict:
    started = time.monotonic()
    domains = schedule_domains(schedule, phase)
    prefix_min, suffix_min = cost_bounds(domains)
    top, top_stats = expand_side("top", cut, domains, TARGET_U, prefix_min, suffix_min, report)
    bottom, bottom_stats = expand_side(
        "bottom", cut, domains, TARGET_U, prefix_min, suffix_min, report
    )
    result = join(top, bottom, TARGET_U)
    result["best_examples"] = result["best_examples"][:1]
    if result["witness"] is not None:
        validation = run_check(N, result["witness"], expected_u=TARGET_U)
        if not validation["all_ok"]:
            raise AssertionError("witness failed independent construction_lab replay")
        result["independent_validation"] = validation
    return {
        "schedule": schedule,
        "operation_word": SCHEDULES[schedule],
        "phase": phase,
        "cut": cut,
        "row_domain_sizes": [len(domain) for domain in domains],
        "row_u_costs": [domain[0].bit_count() for domain in domains],
        "top_states": len(top),
        "bottom_states": len(bottom),
        "top_stats": [asdict(item) for item in top_stats],
        "bottom_stats": [asdict(item) for item in bottom_stats],
        "result": result,
        "elapsed_seconds": time.monotonic() - started,
    }


def run(cut: int = 11, mixed_caps: bool = True, report: bool = False) -> dict:
    phase_names = tuple(PHASES) if mixed_caps else ("main_diagonal", "anti_diagonal")
    families = []
    witness = None
    for phase in phase_names:
        for schedule in SCHEDULES:
            family = run_family(schedule, phase, cut, report)
            families.append(family)
            if witness is None and family["result"]["witness"] is not None:
                witness = family["result"]["witness"]
    source = load_pattern(SOURCE)
    return {
        "schema": SCHEMA,
        "status": "SAT" if witness is not None else "UNSAT_IN_DECLARED_FAMILIES",
        "exact_in_declared_families": True,
        "scope": {
            "source_n": 20,
            "target_n": N,
            "target_u": TARGET_U,
            "schedules": list(SCHEDULES),
            "phases": list(phase_names),
            "caps": "fixed affine n23 rows 0..2 and 21..22, with only the explicitly named top/bottom orientations",
            "attachment_rows": list(ATTACHMENT_ROWS),
            "attachment_packets_main_phase": list(ATTACHMENT_PACKETS),
            "rewrite_radius_packets": REWRITE_RADIUS,
            "rewrite_packet_indices_main_phase": list(REWRITE_PACKETS),
            "rewrite_alphabet": "all eight binary three-cell packets, including charge-one A/S/B and empty E",
            "advance_rows": "the complete old exact-charge radius-one basic seam domains, enlarged only on attachment rows by the declared full-binary window",
            "hold_rows": "the complete old 65-row basic domain, enlarged only on attachment row 5 by the declared full-binary window",
            "negative_scope_note": "Rows 5 and 20 are independent exact-charge rewrites. No other mutable row, schedule, cap content, or unrestricted packet product is included.",
        },
        "source": {"path": SOURCE.name, "sha256": rows_sha256(source), "u_count": 250},
        "families": families,
        "witness": witness,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cut", type=int, default=11)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--witness", type=Path, default=DEFAULT_WITNESS)
    parser.add_argument("--no-mixed-caps", action="store_true")
    parser.add_argument("--report", action="store_true")
    args = parser.parse_args()
    record = run(args.cut, not args.no_mixed_caps, args.report)
    args.output.write_text(json.dumps(record, indent=2) + "\n")
    if record["witness"] is not None:
        args.witness.write_text("\n".join(record["witness"]) + "\n")
    print(f"wrote {args.output}: {record['status']}")


if __name__ == "__main__":
    main()
