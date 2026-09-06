#!/usr/bin/env python3
"""Exact 249-U search in a 22-packet corridor around the phase witness.

The mutable scope is the exact upper phase path where the phase witness differs
from KNOWN_249_NEAR, plus the complete rows 14..17 by packet columns 0..2
lower-left defect rectangle. Every mutable packet ranges over L/X/R/H; every
other packet and the primary cap are frozen to the corrected phase witness.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import signal
from dataclasses import asdict, dataclass
from itertools import combinations
from math import comb
from pathlib import Path

from analysis.patterns.construction_lab import dual_connectivity_check, forest_completion_check, run_check
from analysis.searches.search_residue_two_middle import BASIC_ALPHABET, KNOWN_249_NEAR
from analysis.searches.search_residue_two_suffix_corridor import PathNode, _add_candidate, _reconstruct
from analysis.tiles.tile_grammar import FrontierState, advance_row, initial_state, row_mask, stream_row_packets
from analysis._paths import ANALYSIS_ROOT, analysis_path, source_path


N = 20
TARGET_U = 249
PACKET_COUNT = 6
PHASE_PATH_PACKETS = (
    (4, 0), (4, 1), (5, 0), (5, 1), (6, 0), (6, 1),
    (7, 1), (7, 2), (8, 2), (9, 2),
)
LOWER_DEFECT_PACKETS = tuple((row, column) for row in range(14, 18) for column in range(3))
MUTABLE_PACKETS = PHASE_PATH_PACKETS + LOWER_DEFECT_PACKETS
MUTABLE_BY_ROW = {
    row: tuple(column for candidate_row, column in MUTABLE_PACKETS if candidate_row == row)
    for row in range(N)
}
DISTRIBUTIONS = ((19, 1), (18, 2), (17, 3))
PHASE_WITNESS = analysis_path("residue_two_phase_front_witness.txt")
DEFAULT_CERTIFICATE = analysis_path("residue_two_phase_packet_corridor_22_result.json")
DEFAULT_WITNESS = analysis_path("residue_two_phase_packet_corridor_22_witness.txt")


@dataclass(frozen=True, slots=True)
class RowStats:
    row: int
    mutable_packet_columns: tuple[int, ...]
    incoming_states: int
    packet_extensions: int
    viable_transitions: int
    outgoing_states: int
    assignments_represented: int
    frontier_sha256: str


def payload_sha256(rows: list[str] | tuple[str, ...]) -> str:
    return hashlib.sha256(("\n".join(rows) + "\n").encode("ascii")).hexdigest()


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def phase_rows() -> list[str]:
    rows = PHASE_WITNESS.read_text().splitlines()
    if len(rows) != N or any(len(row) != N for row in rows):
        raise AssertionError("phase witness must be 20x20")
    return rows


def packet_name(rows: list[str], row: int, column: int) -> str:
    value = rows[row][1 + 3 * column : 4 + 3 * column]
    names = [name for name, packet in BASIC_ALPHABET.items() if packet == value]
    if len(names) != 1:
        raise AssertionError(f"packet {(row, column)}={value!r} is outside L/X/R/H")
    return names[0]


def differing_packets(rows: list[str]) -> tuple[tuple[int, int], ...]:
    return tuple(
        (row, column)
        for row in range(N)
        for column in range(PACKET_COUNT)
        if rows[row][1 + 3 * column : 4 + 3 * column]
        != KNOWN_249_NEAR[row][1 + 3 * column : 4 + 3 * column]
    )


def validate_scope(rows: list[str]) -> None:
    if sum(row.count("U") for row in rows) != 250:
        raise AssertionError("corrected phase witness must have 250 U")
    if not dual_connectivity_check(rows)[0] or not forest_completion_check(rows)[0]:
        raise AssertionError("corrected phase witness is not valid")
    expected_differences = PHASE_PATH_PACKETS + (
        (14, 0), (14, 1), (14, 2), (15, 0), (15, 2),
        (16, 0), (16, 1), (16, 2), (17, 0), (17, 1),
    )
    if differing_packets(rows) != expected_differences:
        raise AssertionError("phase/KNOWN_249_NEAR packet differences changed")
    if len(MUTABLE_PACKETS) != 22 or len(set(MUTABLE_PACKETS)) != 22:
        raise AssertionError("mutable scope is not exactly 22 packets")
    for row in sorted({candidate_row for candidate_row, _ in MUTABLE_PACKETS}):
        for column in range(PACKET_COUNT):
            packet_name(rows, row, column)


def fixed_u(rows: list[str]) -> int:
    mutable_u = sum(
        rows[row][1 + 3 * column : 4 + 3 * column].count("U")
        for row, column in MUTABLE_PACKETS
    )
    return sum(row.count("U") for row in rows) - mutable_u


def frontier_sha256(layer: dict[FrontierState, PathNode]) -> str:
    records = sorted(
        (
            state.n, state.row_index, state.previous_u_mask, state.partition,
            state.u_cost, state.cycle_excess, node.ways,
        )
        for state, node in layer.items()
    )
    return hashlib.sha256(json.dumps(records, separators=(",", ":")).encode("ascii")).hexdigest()


def domains(rows: list[str], row: int) -> tuple[tuple[str, ...], ...]:
    mutable = set(MUTABLE_BY_ROW[row])
    return tuple(
        tuple(BASIC_ALPHABET) if column in mutable else (packet_name(rows, row, column),)
        for column in range(PACKET_COUNT)
    )


def future_bounds(rows: list[str], after_row: int) -> tuple[int, int]:
    minimum = maximum = 0
    mutable = set(MUTABLE_PACKETS)
    for row in range(after_row + 1, N):
        minimum += (rows[row][0] == "U") + (rows[row][-1] == "U")
        maximum += (rows[row][0] == "U") + (rows[row][-1] == "U")
        for column in range(PACKET_COUNT):
            if (row, column) in mutable:
                minimum += 2
                maximum += 3
            else:
                cost = rows[row][1 + 3 * column : 4 + 3 * column].count("U")
                minimum += cost
                maximum += cost
    return minimum, maximum


def corridor_after_row17(
    rows: list[str], *, report: bool = True,
) -> tuple[dict[FrontierState, PathNode], list[RowStats]]:
    validate_scope(rows)
    root = PathNode(initial_state(N), 1, None, None)
    layer = {root.state: root}
    stats = []
    for row in range(18):
        incoming = len(layer)
        candidates: dict[FrontierState, PathNode] = {}
        attempted = live = 0
        lower, upper = future_bounds(rows, row)
        if MUTABLE_BY_ROW[row]:
            for parent in layer.values():
                transitions, count = stream_row_packets(
                    parent.state, rows[row][0], rows[row][-1], domains(rows, row),
                    packet_alphabet=BASIC_ALPHABET,
                    u_cost_bounds=(TARGET_U - upper, TARGET_U - lower),
                )
                attempted += count
                live += len(transitions)
                for transition in transitions:
                    _add_candidate(candidates, transition.outgoing, parent, transition.row_mask)
        else:
            mask = row_mask(rows[row])
            attempted = incoming
            for parent in layer.values():
                child = advance_row(parent.state, mask)
                if child is None or not TARGET_U - upper <= child.u_cost <= TARGET_U - lower:
                    continue
                live += 1
                _add_candidate(candidates, child, parent, mask)
        layer = candidates
        item = RowStats(
            row, MUTABLE_BY_ROW[row], incoming, attempted, live, len(layer),
            sum(node.ways for node in layer.values()), frontier_sha256(layer),
        )
        stats.append(item)
        if report:
            print(
                f"row={row} mutable={list(item.mutable_packet_columns)} incoming={incoming} "
                f"extensions={attempted} live={live} states={len(layer)} "
                f"assignments={item.assignments_represented}", flush=True,
            )
    return layer, stats


def advance_layer(
    layer: dict[FrontierState, PathNode], masks: tuple[int, ...]
) -> tuple[dict[FrontierState, PathNode], int]:
    outgoing: dict[FrontierState, PathNode] = {}
    live = 0
    for parent in layer.values():
        for mask in masks:
            child = advance_row(parent.state, mask)
            if child is not None:
                live += 1
                _add_candidate(outgoing, child, parent, mask)
    return outgoing, live


def accepted(layer: dict[FrontierState, PathNode]) -> dict[FrontierState, PathNode]:
    result = {}
    for state, node in layer.items():
        if state.u_cost != TARGET_U:
            continue
        candidate = _reconstruct(node)
        if dual_connectivity_check(candidate)[0] and forest_completion_check(candidate)[0]:
            result[state] = node
    return result


def masks_with_u_count(count: int) -> tuple[int, ...]:
    return tuple(sum(1 << column for column in columns) for columns in combinations(range(N), count))


def cap_search(
    corridor: dict[FrontierState, PathNode], rows: list[str], distribution: tuple[int, int] | None,
) -> tuple[dict, list[str] | None]:
    layer = corridor
    row_records = []
    counts = distribution or (rows[18].count("U"), rows[19].count("U"))
    for row, count in zip((18, 19), counts):
        masks = (row_mask(rows[row]),) if distribution is None else masks_with_u_count(count)
        incoming = len(layer)
        incoming_ways = sum(node.ways for node in layer.values())
        layer, live = advance_layer(layer, masks)
        row_records.append({
            "row": row, "u_count": count, "masks": len(masks),
            "incoming_states": incoming, "transitions_attempted": incoming * len(masks),
            "incoming_assignments": incoming_ways, "live_transitions": live,
            "outgoing_states": len(layer),
            "assignments_represented": sum(node.ways for node in layer.values()),
            "frontier_sha256": frontier_sha256(layer),
        })
    accepted_layer = accepted(layer)
    witness = _reconstruct(next(iter(accepted_layer.values()))) if accepted_layer else None
    return {
        "distribution": list(counts), "rows": row_records,
        "final_states": len(layer), "final_assignments": sum(node.ways for node in layer.values()),
        "accepted_states": len(accepted_layer),
        "accepted_assignments": sum(node.ways for node in accepted_layer.values()),
        "result": "positive" if accepted_layer else "negative",
    }, witness


def provenance(rows: list[str]) -> dict:
    directory = ANALYSIS_ROOT
    files = {
        "generator": Path(__file__),
        "phase_witness": PHASE_WITNESS,
        "base_pattern_source": source_path('search_residue_two_middle.py'),
        "frontier_kernel": source_path('tile_grammar.py'),
    }
    return {
        "phase_witness_rows_sha256": payload_sha256(rows),
        "known_249_near_rows_sha256": payload_sha256(KNOWN_249_NEAR),
        "canonical_encoding": "ASCII rows joined by LF with one final LF",
        "source_files": {
            name: {"path": path.name, "sha256": file_sha256(path)} for name, path in files.items()
        },
    }


def scope(rows: list[str]) -> dict:
    differences = differing_packets(rows)
    fixed = fixed_u(rows)
    required_h = TARGET_U - fixed - 2 * len(MUTABLE_PACKETS)
    return {
        "base": "analysis/residue_two_phase_front_witness.txt",
        "comparison": "search_residue_two_middle.KNOWN_249_NEAR",
        "n": N, "target_u": TARGET_U,
        "phase_witness_u": sum(row.count("U") for row in rows),
        "phase_vs_near_differing_packets": [list(value) for value in differences],
        "phase_path_packets": [list(value) for value in PHASE_PATH_PACKETS],
        "lower_defect_rectangle": {"rows": [14, 17], "packet_columns": [0, 2]},
        "mutable_packets": [list(value) for value in MUTABLE_PACKETS],
        "mutable_packet_count": len(MUTABLE_PACKETS),
        "alphabet": list(BASIC_ALPHABET),
        "outside_mutable_packets": "frozen exactly to the corrected phase witness",
        "primary_cap_rows": [18, 19], "primary_cap_u_distribution": [18, 2],
        "fixed_u_primary": fixed, "required_h_packets_primary": required_h,
        "charge_feasible_assignments_before_topology": comb(len(MUTABLE_PACKETS), required_h) * 3 ** (len(MUTABLE_PACKETS) - required_h),
        "alternate_cap_distributions": [list(value) for value in DISTRIBUTIONS],
        "deduplication_key": "full FrontierState", "exact_multiplicities": True,
        "beam": None, "state_cap": None, "partition_projection": None,
    }


def _timeout(_signum: int, _frame: object) -> None:
    raise TimeoutError


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--quiet", action="store_true")
    parser.add_argument("--max-seconds", type=int, default=480)
    parser.add_argument("--certificate", type=Path, default=DEFAULT_CERTIFICATE)
    parser.add_argument("--witness", type=Path, default=DEFAULT_WITNESS)
    args = parser.parse_args()
    if args.max_seconds < 1:
        parser.error("--max-seconds must be positive")
    rows = phase_rows()
    completed_rows: list[dict] = []
    record = {
        "schema": "grid-graphs.residue-two-phase-packet-corridor-22.v1",
        "exact": False, "provenance": provenance(rows), "scope": scope(rows),
        "result": "incomplete", "completed_rows": completed_rows,
        "corridor_after_row17": None, "fixed_cap": None, "alternate_caps": None,
        "witness": None,
    }
    old_handler = signal.signal(signal.SIGALRM, _timeout)
    signal.alarm(args.max_seconds)
    try:
        corridor, stats = corridor_after_row17(rows, report=not args.quiet)
        completed_rows.extend(asdict(item) for item in stats)
        record["corridor_after_row17"] = {
            "states": len(corridor), "assignments": sum(node.ways for node in corridor.values()),
            "u_costs": sorted({state.u_cost for state in corridor}),
            "frontier_sha256": frontier_sha256(corridor),
        }
        fixed, witness = cap_search(corridor, rows, None)
        record["fixed_cap"] = fixed
        if fixed["result"] == "negative":
            alternates = []
            for distribution in DISTRIBUTIONS:
                item, candidate = cap_search(corridor, rows, distribution)
                alternates.append(item)
                witness = witness or candidate
                if not args.quiet:
                    print(
                        f"cap={distribution} row18_states={item['rows'][0]['outgoing_states']} "
                        f"row19_states={item['rows'][1]['outgoing_states']} "
                        f"accepted_assignments={item['accepted_assignments']}", flush=True,
                    )
            record["alternate_caps"] = alternates
        record["exact"] = True
        record["result"] = "positive" if witness else "negative"
        record["witness"] = witness
    except TimeoutError:
        record["stop_reason"] = f"time limit reached after {args.max_seconds} seconds; no exact-negative claim"
    finally:
        signal.alarm(0)
        signal.signal(signal.SIGALRM, old_handler)
    args.certificate.write_text(json.dumps(record, indent=2) + "\n")
    if not record["exact"]:
        print("INCOMPLETE: 480-second-bounded exact search did not finish; no exact-negative claim.")
        print(f"certificate={args.certificate}")
        raise SystemExit(2)
    if record["witness"]:
        info = run_check(N, record["witness"], verbose=not args.quiet)
        if not info["all_ok"]:
            raise AssertionError(f"run_check rejected witness: {info}")
        args.witness.write_text("\n".join(record["witness"]) + "\n")
        print(f"EXACT POSITIVE witness={args.witness}")
    else:
        print("EXACT NEGATIVE in the fixed and three declared alternate-cap scopes.")
    print(f"certificate={args.certificate}")


if __name__ == "__main__":
    main()
