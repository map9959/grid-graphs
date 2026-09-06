#!/usr/bin/env python3
"""Exact two-lobe phase-front corridor search around the corrected witness.

Rows 0..3 and 10..13 are fixed.  In rows 4..9 and 14..17, packet columns
3..5 are fixed and columns 0..2 vary, subject to the complete row belonging
to the basic width-6 language L*(X|H)+R* with center width at most five.
The fixed cap and exact cap distributions (19,1), (18,2), and (17,3) are all
tested at exactly 249 U.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import signal
from dataclasses import asdict, dataclass
from itertools import combinations
from pathlib import Path

from analysis._paths import ANALYSIS_ROOT, analysis_path, source_path
from analysis.patterns.construction_lab import run_check
from analysis.searches.search_residue_two_middle import BASIC_ALPHABET, KNOWN_249_NEAR
from analysis.searches.search_residue_two_phase_front import (
    MAX_CENTER_WIDTH,
    _packet_names,
    row_words,
)
from analysis.searches.search_residue_two_phase_packet_corridor_22 import phase_rows
from analysis.searches.search_residue_two_suffix_corridor import (
    PathNode,
    _add_candidate,
    _reconstruct,
)
from analysis.tiles.tile_grammar import (
    FrontierState,
    advance_row,
    initial_state,
    row_mask,
)

N = 20
TARGET_U = 249
PACKET_COUNT = 6
MUTABLE_ROWS = (*range(4, 10), *range(14, 18))
FIXED_BODY_ROWS = (*range(0, 4), *range(10, 14))
MUTABLE_PACKET_COLUMNS = (0, 1, 2)
FROZEN_PACKET_COLUMNS = (3, 4, 5)
CAP_DISTRIBUTIONS = ((19, 1), (18, 2), (17, 3))
DEFAULT_RESULT = analysis_path("residue_two_two_lobe_phase_corridor_result.json")
DEFAULT_WITNESS = analysis_path("residue_two_two_lobe_phase_corridor_witness.txt")


@dataclass(frozen=True, slots=True)
class RowStats:
    row: int
    kind: str
    domain_size: int
    incoming_states: int
    transitions_attempted: int
    viable_transitions: int
    outgoing_states: int
    assignments_represented: int
    frontier_sha256: str


def rows_sha256(rows: list[str] | tuple[str, ...]) -> str:
    return hashlib.sha256(("\n".join(rows) + "\n").encode("ascii")).hexdigest()


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def frontier_sha256(layer: dict[FrontierState, PathNode]) -> str:
    records = sorted(
        (
            state.n,
            state.row_index,
            state.previous_u_mask,
            state.partition,
            state.u_cost,
            state.cycle_excess,
            node.ways,
        )
        for state, node in layer.items()
    )
    return hashlib.sha256(
        json.dumps(records, separators=(",", ":")).encode("ascii")
    ).hexdigest()


def mutable_row_words(rows: list[str], row: int) -> tuple[str, ...]:
    if row not in MUTABLE_ROWS:
        raise ValueError(f"row {row} is not mutable")
    frozen_right = _packet_names(rows[row])[3:]
    return tuple(word for word in row_words(PACKET_COUNT, "basic") if word[3:] == frozen_right)


def render_word(word: str) -> str:
    return "." + "".join(BASIC_ALPHABET[name] for name in word) + "."


def row_domains(rows: list[str]) -> dict[int, tuple[str, ...]]:
    return {
        row: tuple(render_word(word) for word in mutable_row_words(rows, row))
        for row in MUTABLE_ROWS
    }


def validate_scope(rows: list[str]) -> None:
    if len(rows) != N or any(len(row) != N for row in rows):
        raise AssertionError("corrected phase witness must be 20x20")
    if sum(row.count("U") for row in rows) != 250:
        raise AssertionError("corrected phase witness must have 250 U")
    if set(BASIC_ALPHABET) != {"L", "X", "R", "H"}:
        raise AssertionError("basic alphabet changed")
    if MAX_CENTER_WIDTH != 5:
        raise AssertionError("phase-front center bound changed")
    domains = row_domains(rows)
    expected_sizes = (15, 15, 22, 22, 22, 22, 22, 22, 22, 22)
    if tuple(map(len, domains.values())) != expected_sizes:
        raise AssertionError("two-lobe row domain sizes changed")
    for candidate_name, candidate in (
        ("corrected phase witness", rows),
        ("KNOWN_249_NEAR", KNOWN_249_NEAR),
    ):
        if any(candidate[row] != rows[row] for row in FIXED_BODY_ROWS):
            raise AssertionError(f"{candidate_name} does not match the fixed body rows")
        if any(candidate[row] not in domains[row] for row in MUTABLE_ROWS):
            raise AssertionError(f"{candidate_name} is absent from a mutable row domain")
        if any(candidate[row] != rows[row] for row in (18, 19)):
            raise AssertionError(f"{candidate_name} does not match the fixed cap")


def future_body_bounds(
    rows: list[str], domains: dict[int, tuple[str, ...]], after_row: int
) -> tuple[int, int]:
    minimum = maximum = 20  # Every declared two-row cap distribution has 20 U.
    for row in range(after_row + 1, 18):
        choices = domains.get(row, (rows[row],))
        costs = tuple(choice.count("U") for choice in choices)
        minimum += min(costs)
        maximum += max(costs)
    return minimum, maximum


def body_search(
    rows: list[str], *, report: bool = True, checkpoints: list[dict] | None = None
) -> tuple[dict[FrontierState, PathNode], list[RowStats]]:
    validate_scope(rows)
    domains = row_domains(rows)
    root = PathNode(initial_state(N), 1, None, None)
    layer = {root.state: root}
    stats = []
    for row in range(18):
        choices = domains.get(row, (rows[row],))
        masks = tuple(row_mask(choice) for choice in choices)
        incoming = len(layer)
        attempted = incoming * len(masks)
        viable = 0
        outgoing: dict[FrontierState, PathNode] = {}
        future_min, future_max = future_body_bounds(rows, domains, row)
        for parent in layer.values():
            for mask in masks:
                child = advance_row(parent.state, mask)
                if child is None or not TARGET_U - future_max <= child.u_cost <= TARGET_U - future_min:
                    continue
                viable += 1
                _add_candidate(outgoing, child, parent, mask)
        layer = outgoing
        item = RowStats(
            row=row,
            kind="phase-front-domain" if row in MUTABLE_ROWS else "fixed",
            domain_size=len(masks),
            incoming_states=incoming,
            transitions_attempted=attempted,
            viable_transitions=viable,
            outgoing_states=len(layer),
            assignments_represented=sum(node.ways for node in layer.values()),
            frontier_sha256=frontier_sha256(layer),
        )
        stats.append(item)
        if checkpoints is not None:
            checkpoints.append(asdict(item))
        if report:
            print(
                f"row={row} kind={item.kind} domain={item.domain_size} "
                f"incoming={incoming} attempted={attempted} viable={viable} "
                f"states={len(layer)} assignments={item.assignments_represented}",
                flush=True,
            )
    return layer, stats


def masks_with_u_count(count: int) -> tuple[int, ...]:
    return tuple(
        sum(1 << column for column in columns)
        for columns in combinations(range(N), count)
    )


def cap_search(
    corridor: dict[FrontierState, PathNode],
    rows: list[str],
    distribution: tuple[int, int] | None,
) -> tuple[dict, list[str] | None]:
    layer = corridor
    records = []
    counts = distribution or (rows[18].count("U"), rows[19].count("U"))
    for row, count in zip((18, 19), counts):
        masks = (row_mask(rows[row]),) if distribution is None else masks_with_u_count(count)
        incoming = len(layer)
        outgoing: dict[FrontierState, PathNode] = {}
        viable = 0
        for parent in layer.values():
            for mask in masks:
                child = advance_row(parent.state, mask)
                if child is None:
                    continue
                viable += 1
                _add_candidate(outgoing, child, parent, mask)
        layer = outgoing
        records.append({
            "row": row,
            "u_count": count,
            "mask_count": len(masks),
            "incoming_states": incoming,
            "transitions_attempted": incoming * len(masks),
            "viable_transitions": viable,
            "outgoing_states": len(layer),
            "assignments_represented": sum(node.ways for node in layer.values()),
            "frontier_sha256": frontier_sha256(layer),
        })
    accepted = {state: node for state, node in layer.items() if state.u_cost == TARGET_U}
    witness = _reconstruct(next(iter(accepted.values()))) if accepted else None
    return {
        "kind": "fixed" if distribution is None else "all masks with exact row U counts",
        "distribution": list(counts),
        "rows": records,
        "final_states": len(layer),
        "final_assignments": sum(node.ways for node in layer.values()),
        "accepted_states": len(accepted),
        "accepted_assignments": sum(node.ways for node in accepted.values()),
        "result": "positive" if accepted else "negative",
    }, witness


def independent_validate(rows: list[str], base: list[str]) -> dict:
    info = run_check(N, rows, verbose=False)
    domains = row_domains(base)
    scope_ok = (
        all(rows[row] == base[row] for row in FIXED_BODY_ROWS)
        and all(rows[row] in domains[row] for row in MUTABLE_ROWS)
    )
    cap_distribution_ok = (rows[18].count("U"), rows[19].count("U")) in CAP_DISTRIBUTIONS
    result = {
        **info,
        "scope_ok": scope_ok,
        "cap_distribution_ok": cap_distribution_ok,
        "rows_sha256": rows_sha256(rows),
    }
    if not info["all_ok"] or not scope_ok or not cap_distribution_ok:
        raise AssertionError(f"independent validation rejected witness: {result}")
    return result


def provenance(rows: list[str]) -> dict:
    directory = ANALYSIS_ROOT
    files = {
        "generator": Path(__file__),
        "phase_witness": directory / "residue_two_phase_front_witness.txt",
        "phase_front_kernel": source_path('search_residue_two_phase_front.py'),
        "corridor_kernel": source_path('search_residue_two_suffix_corridor.py'),
        "frontier_kernel": source_path('tile_grammar.py'),
        "known_near_source": source_path('search_residue_two_middle.py'),
    }
    return {
        "canonical_rows": "ASCII rows joined by LF with one final LF",
        "phase_witness_rows_sha256": rows_sha256(rows),
        "known_249_near_rows_sha256": rows_sha256(KNOWN_249_NEAR),
        "source_files": {
            name: {"path": path.name, "sha256": file_sha256(path)}
            for name, path in files.items()
        },
    }


def scope(rows: list[str]) -> dict:
    domains = row_domains(rows)
    return {
        "base": "analysis/residue_two_phase_front_witness.txt",
        "n": N,
        "target_u": TARGET_U,
        "fixed_body_rows": [[0, 3], [10, 13]],
        "mutable_row_lobes": [[4, 9], [14, 17]],
        "mutable_packet_columns": list(MUTABLE_PACKET_COLUMNS),
        "frozen_packet_columns_in_every_mutable_row": list(FROZEN_PACKET_COLUMNS),
        "row_language": "L*(X|H)+R*",
        "center_width_max": MAX_CENTER_WIDTH,
        "packet_count": PACKET_COUNT,
        "row_domains": {
            str(row): {
                "frozen_right_word": _packet_names(rows[row])[3:],
                "size": len(domains[row]),
                "words": list(mutable_row_words(rows, row)),
                "rows_sha256": rows_sha256(domains[row]),
            }
            for row in MUTABLE_ROWS
        },
        "contains_corrected_phase_witness_geometry": True,
        "contains_known_249_near_geometry": True,
        "fixed_cap_rows": [18, 19],
        "fixed_cap_distribution": [rows[18].count("U"), rows[19].count("U")],
        "tested_cap_distributions": [list(value) for value in CAP_DISTRIBUTIONS],
        "deduplication_key": "full unprojected FrontierState",
        "exact_multiplicities": True,
        "beam": None,
        "projection": None,
        "state_cap": None,
    }


def _timeout(_signum: int, _frame: object) -> None:
    raise TimeoutError


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--quiet", action="store_true")
    parser.add_argument("--max-seconds", type=int, default=480)
    parser.add_argument("--result", type=Path, default=DEFAULT_RESULT)
    parser.add_argument("--witness", type=Path, default=DEFAULT_WITNESS)
    args = parser.parse_args()
    if not 1 <= args.max_seconds <= 480:
        parser.error("--max-seconds must be in 1..480")

    rows = phase_rows()
    validate_scope(rows)
    completed_rows: list[dict] = []
    record = {
        "schema": "grid-graphs.residue-two-two-lobe-phase-corridor.v1",
        "exact": False,
        "result": "incomplete",
        "provenance": provenance(rows),
        "scope": scope(rows),
        "completed_body_rows": completed_rows,
        "corridor_after_row17": None,
        "fixed_cap": None,
        "cap_distributions": [],
        "witness": None,
        "independent_validation": None,
    }
    old_handler = signal.signal(signal.SIGALRM, _timeout)
    signal.alarm(args.max_seconds)
    try:
        corridor, _ = body_search(
            rows, report=not args.quiet, checkpoints=completed_rows
        )
        record["corridor_after_row17"] = {
            "states": len(corridor),
            "assignments_represented": sum(node.ways for node in corridor.values()),
            "u_costs": sorted({state.u_cost for state in corridor}),
            "frontier_sha256": frontier_sha256(corridor),
        }
        fixed, witness = cap_search(corridor, rows, None)
        record["fixed_cap"] = fixed
        for distribution in CAP_DISTRIBUTIONS:
            cap, candidate = cap_search(corridor, rows, distribution)
            record["cap_distributions"].append(cap)
            witness = witness or candidate
            if not args.quiet:
                print(
                    f"cap={distribution} final_states={cap['final_states']} "
                    f"accepted_assignments={cap['accepted_assignments']}",
                    flush=True,
                )
        if witness is not None:
            record["independent_validation"] = independent_validate(witness, rows)
            record["witness"] = witness
        record["exact"] = True
        record["result"] = "positive" if witness is not None else "negative"
    except TimeoutError:
        record["stop_reason"] = (
            f"time limit reached after {args.max_seconds} seconds; search incomplete; "
            "no negative claim"
        )
    finally:
        signal.alarm(0)
        signal.signal(signal.SIGALRM, old_handler)
        args.result.write_text(json.dumps(record, indent=2) + "\n")

    if not record["exact"]:
        print("INCOMPLETE: bounded exact search timed out; no negative claim.")
        print(f"result={args.result}")
        raise SystemExit(2)
    if record["witness"] is not None:
        args.witness.write_text("\n".join(record["witness"]) + "\n")
        print(f"EXACT POSITIVE witness={args.witness}")
    else:
        print("EXACT NEGATIVE in the fixed cap and three declared cap distributions.")
    print(f"result={args.result}")


if __name__ == "__main__":
    main()
