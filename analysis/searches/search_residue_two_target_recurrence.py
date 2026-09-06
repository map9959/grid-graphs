#!/usr/bin/env python3
"""Exact fixed-word B20-to-n23 target-charge recurrence search.

The two initial schedule words are A^5 H^3 A^15 and A^8 H^3 A^12.
Mutable ADVANCE rows are literal B20 packet words widened on the left or right;
HOLD rows are all seven L^a H R^(6-a) charge-one rows.  The shared top-three
and bottom-two cap rows are fixed in a D4-consistent affine n23 phase.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import time
from dataclasses import asdict
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
from analysis.searches.search_residue_two_phase_front import _packet_names, row_words
from analysis.tiles.tile_grammar import ROW_PACKET_ALPHABET, row_mask

HERE = ANALYSIS_ROOT
DEFAULT_OUTPUT = HERE / "residue_two_n23_target_recurrence_result.json"
DEFAULT_WITNESS = HERE / "residue_two_n23_target_recurrence_witness.txt"
SCHEMA = "grid-graphs.residue-two-target-recurrence.v1"
N = 23
TARGET_U = 333
PACKETS = 7
CAP_ROWS = (0, 1, 2, 21, 22)
SCHEDULES = {
    "A5_H3_A15": "A" * 5 + "H" * 3 + "A" * 15,
    "A8_H3_A12": "A" * 8 + "H" * 3 + "A" * 12,
}


def compose_mutable_words(intermediate: str, target: str) -> str:
    cursor = 0
    output = []
    for operation in target:
        if operation == "H":
            output.append("H")
        else:
            output.append(intermediate[cursor])
            cursor += 1
    if cursor != len(intermediate):
        raise AssertionError("mutable composition did not consume its intermediate word")
    return "".join(output)


INTERMEDIATE_MUTABLE = {
    "P2": "A" * 2 + "H" * 3 + "A" * 10,
    "P5": "A" * 5 + "H" * 3 + "A" * 7,
}
TARGET_MUTABLE = {
    "P2": "A" * 2 + "H" * 3 + "A" * 13,
    "P5": "A" * 5 + "H" * 3 + "A" * 10,
}
DIRECT_SCHEDULES = {
    f"direct_{left}_{right}": compose_mutable_words(intermediate, TARGET_MUTABLE[right])
    for left, intermediate in INTERMEDIATE_MUTABLE.items()
    for right in TARGET_MUTABLE
}


def rows_sha256(rows: list[str] | tuple[str, ...]) -> str:
    return hashlib.sha256(("\n".join(rows) + "\n").encode("ascii")).hexdigest()


def orient(rows: tuple[str, ...] | list[str], phase: str) -> tuple[str, ...]:
    values = tuple(rows)
    if phase == "main_diagonal":
        return values
    if phase == "anti_diagonal":
        return tuple(row[::-1] for row in values)
    raise ValueError("phase must be main_diagonal or anti_diagonal")


def render_word(word: str) -> str:
    return "." + "".join(ROW_PACKET_ALPHABET[symbol] for symbol in word) + "."


def widened_rows(source_row: str, radius: int = 1) -> tuple[str, ...]:
    word = _packet_names(source_row)
    if len(word) != 6:
        raise ValueError("B20 mutable rows must contain six packets")
    target_u = source_row.count("U") + 2
    alphabet = tuple(ROW_PACKET_ALPHABET)
    return tuple(
        dict.fromkeys(
            row
            for seam in range(PACKETS)
            for candidate in itertools.product(
                *(
                    alphabet
                    if abs(packet - seam) <= radius
                    else (word[packet if packet < seam else packet - 1],)
                    for packet in range(PACKETS)
                )
            )
            if (row := render_word("".join(candidate))).count("U") == target_u
        )
    )


def hold_rows() -> tuple[str, ...]:
    return tuple(
        render_word(word)
        for word in row_words(PACKETS, "basic")
        if word.count("H") == 1
    )


def direct_widened_rows(source_row: str, radius: int = 1) -> tuple[str, ...]:
    word = _packet_names(source_row)
    if len(word) != 5:
        raise ValueError("A17 mutable rows must contain five packets")
    target_u = source_row.count("U") + 4
    alphabet = tuple(ROW_PACKET_ALPHABET)
    return tuple(
        dict.fromkeys(
            row
            for seam in range(6)
            for candidate in itertools.product(
                *(
                    alphabet
                    if seam - radius <= packet <= seam + 1 + radius
                    else (word[packet if packet < seam else packet - 2],)
                    for packet in range(PACKETS)
                )
            )
            if (row := render_word("".join(candidate))).count("U") == target_u
        )
    )


def schedule_domains(schedule: str, phase: str) -> tuple[tuple[int, ...], ...]:
    if schedule in DIRECT_SCHEDULES:
        return direct_schedule_domains(schedule, phase)
    try:
        operations = SCHEDULES[schedule]
    except KeyError as error:
        raise ValueError(f"unknown schedule {schedule}") from error
    source = orient(load_pattern(SOURCE), phase)
    cap = orient(residue_two_affine_pattern(N), phase)
    domains = []
    cursor = 0
    for target_row, operation in enumerate(operations):
        if target_row in CAP_ROWS:
            rows = (cap[target_row],)
        elif operation == "A":
            if not 3 <= cursor <= 17:
                raise AssertionError("mutable ADVANCE row mapped outside the B20 mutable rows")
            rows = widened_rows(source[cursor])
        else:
            rows = hold_rows()
            if phase == "anti_diagonal":
                rows = tuple(row[::-1] for row in rows)
        domains.append(tuple(sorted({row_mask(row) for row in rows})))
        if operation == "A":
            cursor += 1
    if cursor != 20:
        raise AssertionError("schedule does not consume all twenty source rows")
    if sum(min(mask.bit_count() for mask in domain) for domain in domains) != TARGET_U:
        raise AssertionError("declared recurrence domains are not fixed at target charge")
    if any(len({mask.bit_count() for mask in domain}) != 1 for domain in domains):
        raise AssertionError("a recurrence row domain mixes charges")
    return tuple(domains)


def direct_schedule_domains(schedule: str, phase: str) -> tuple[tuple[int, ...], ...]:
    operations = DIRECT_SCHEDULES[schedule]
    if len(operations) != 18 or operations.count("A") != 12 or operations.count("H") != 6:
        raise AssertionError("direct mutable schedule must be a 12-ADVANCE/6-HOLD word")
    source = orient(residue_two_affine_pattern(17), phase)
    cap = orient(residue_two_affine_pattern(N), phase)
    domains = [(row_mask(cap[row]),) for row in range(N)]
    cursor = 3
    for offset, operation in enumerate(operations):
        target_row = offset + 3
        if operation == "A":
            rows = direct_widened_rows(source[cursor])
            cursor += 1
        else:
            rows = hold_rows()
            if phase == "anti_diagonal":
                rows = tuple(row[::-1] for row in rows)
        domains[target_row] = tuple(sorted({row_mask(row) for row in rows}))
    if cursor != 15:
        raise AssertionError("direct schedule did not consume the twelve A17 mutable rows")
    if sum(domain[0].bit_count() for domain in domains) != TARGET_U:
        raise AssertionError("direct width-six scaffold is not fixed at target charge")
    return tuple(domains)


def run_family(schedule: str, phase: str, cut: int, report: bool) -> dict:
    started = time.monotonic()
    domains = schedule_domains(schedule, phase)
    prefix_min, suffix_min = cost_bounds(domains)
    top, top_stats = expand_side(
        "top", cut, domains, TARGET_U, prefix_min, suffix_min, report
    )
    bottom, bottom_stats = expand_side(
        "bottom", cut, domains, TARGET_U, prefix_min, suffix_min, report
    )
    result = join(top, bottom, TARGET_U)
    result["best_examples"] = result["best_examples"][:1]
    if result["witness"] is not None:
        validation = run_check(N, result["witness"], expected_u=TARGET_U)
        if not validation["all_ok"]:
            raise AssertionError("recurrence witness failed independent construction_lab replay")
        result["independent_validation"] = validation
    return {
        "schedule": schedule,
        "operation_word": (
            SCHEDULES[schedule] if schedule in SCHEDULES else DIRECT_SCHEDULES[schedule]
        ),
        "phase": phase,
        "cut": cut,
        "row_domain_sizes": [len(domain) for domain in domains],
        "row_u_costs": [next(iter(domain)).bit_count() for domain in domains],
        "top_states": len(top),
        "bottom_states": len(bottom),
        "top_stats": [asdict(item) for item in top_stats],
        "bottom_stats": [asdict(item) for item in bottom_stats],
        "result": result,
        "elapsed_seconds": time.monotonic() - started,
    }


def run(cut: int = 11, report: bool = False) -> dict:
    families = []
    witness = None
    for phase in ("main_diagonal", "anti_diagonal"):
        for schedule in SCHEDULES:
            family = run_family(schedule, phase, cut, report)
            families.append(family)
            if witness is None and family["result"]["witness"] is not None:
                witness = family["result"]["witness"]
        for schedule in DIRECT_SCHEDULES:
            family = run_family(schedule, phase, cut, report)
            families.append(family)
            if witness is None and family["result"]["witness"] is not None:
                witness = family["result"]["witness"]
    source = load_pattern(SOURCE)
    direct_source = tuple(residue_two_affine_pattern(17))
    record = {
        "schema": SCHEMA,
        "status": "SAT" if witness is not None else "UNSAT_IN_DECLARED_FAMILIES",
        "exact_in_declared_families": True,
        "scope": {
            "source_n": 20,
            "target_n": N,
            "target_u": TARGET_U,
            "schedules": list(SCHEDULES),
            "direct_width_six_schedules": DIRECT_SCHEDULES,
            "phases": ["main_diagonal", "anti_diagonal"],
            "caps": "D4-consistent affine n23 rows 0..2 and 21..22",
            "advance_rows": "all exact-charge basic-packet rows in a radius-one neighborhood of any insertion seam; retained packets outside that neighborhood are fixed to the mapped B20 row",
            "hold_rows": "all 65 canonical L*(X|H)+R* rows of center width at most five with exactly one H, hence charge one",
            "direct_width_six": "all four literal compositions of mutable P2/P5 one-step words, with a contiguous radius-one two-packet slab from A17",
            "negative_scope_note": "Seams are independent between rows (a superset of unit-speed moving seams). No radius-two rewrites, nonbasic phase packets, other HOLD placements, or mixed D4 caps are included.",
        },
        "source": {"path": SOURCE.name, "sha256": rows_sha256(source), "u_count": 250},
        "direct_source": {
            "generator": "diagonal_patterns.residue_two_affine_pattern(17)",
            "sha256": rows_sha256(direct_source),
            "u_count": 179,
        },
        "families": families,
        "witness": witness,
    }
    return record


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cut", type=int, default=11)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--witness", type=Path, default=DEFAULT_WITNESS)
    parser.add_argument("--report", action="store_true")
    args = parser.parse_args()
    record = run(args.cut, args.report)
    args.output.write_text(json.dumps(record, indent=2) + "\n")
    if record["witness"] is not None:
        args.witness.write_text("\n".join(record["witness"]) + "\n")
    print(
        f"wrote {args.output}: {record['status']}; "
        + ", ".join(
            f"{item['phase']}/{item['schedule']}={item['result']['conclusion']}"
            for item in record["families"]
        )
    )


if __name__ == "__main__":
    main()
