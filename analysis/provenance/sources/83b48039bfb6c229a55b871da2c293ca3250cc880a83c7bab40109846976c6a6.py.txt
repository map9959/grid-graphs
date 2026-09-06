#!/usr/bin/env python3
"""Exhaust the exact 21-packet suffix widening around ``KNOWN_250``.

Rows 11..17 and packet columns 0..2 range over L/X/R/H. All other bits are
fixed to KNOWN_250 for the primary search. If that cap is negative, the three
declared exact two-row cap languages are also searched from the row-17 layer.
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

from construction_lab import dual_connectivity_check, forest_completion_check, run_check
from search_residue_two_middle import BASIC_ALPHABET, KNOWN_250
from search_residue_two_suffix_corridor import (
    FIRST_MUTABLE_ROW,
    LAST_MUTABLE_ROW,
    N,
    PACKET_COUNT,
    PathNode,
    RowStats,
    TARGET_U,
    _add_candidate,
    _reconstruct,
    fixed_u_for,
    known_250_sha256,
    layer_after_row17,
)
from tile_grammar import FrontierState, advance_row, row_mask


MUTABLE_PACKET_COLUMNS = (0, 1, 2)
MUTABLE_PACKETS = 21
FIXED_U = fixed_u_for(MUTABLE_PACKET_COLUMNS)
REQUIRED_H_PACKETS = TARGET_U - FIXED_U - 2 * MUTABLE_PACKETS
CHARGE_FEASIBLE_ASSIGNMENTS = (
    comb(MUTABLE_PACKETS, REQUIRED_H_PACKETS)
    * 3 ** (MUTABLE_PACKETS - REQUIRED_H_PACKETS)
)
DISTRIBUTIONS = ((19, 1), (18, 2), (17, 3))
DEFAULT_CERTIFICATE = Path(__file__).with_name("residue_two_suffix_corridor_21_result.json")
DEFAULT_WITNESS = Path(__file__).with_name("residue_two_suffix_corridor_21_witness.txt")


@dataclass(frozen=True, slots=True)
class CapStats:
    row18_u: int
    row19_u: int
    row18_masks: int
    row18_transitions_attempted: int
    row18_live_transitions: int
    row18_states: int
    row18_assignments: int
    row18_frontier_sha256: str
    row19_masks: int
    row19_transitions_attempted: int
    row19_live_transitions: int
    row19_states: int
    row19_assignments: int
    row19_frontier_sha256: str
    accepted_states: int
    accepted_assignments: int


def _sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def provenance() -> dict:
    directory = Path(__file__).parent
    paths = {
        "generator": Path(__file__),
        "corridor_search": directory / "search_residue_two_suffix_corridor.py",
        "base_pattern_source": directory / "search_residue_two_middle.py",
        "frontier_kernel": directory / "tile_grammar.py",
    }
    return {
        "known_250_rows_sha256": known_250_sha256(),
        "source_files": {
            name: {"path": path.name, "sha256": _sha256_file(path)}
            for name, path in paths.items()
        },
    }


def frontier_sha256(layer: dict[FrontierState, PathNode]) -> str:
    """Hash exact states and multiplicities in a deterministic order."""

    records = [
        [
            state.n,
            state.row_index,
            state.previous_u_mask,
            list(state.partition),
            state.u_cost,
            state.cycle_excess,
            node.ways,
        ]
        for state, node in layer.items()
    ]
    records.sort()
    payload = json.dumps(records, separators=(",", ":")).encode("ascii")
    return hashlib.sha256(payload).hexdigest()


def masks_with_u_count(count: int) -> tuple[int, ...]:
    return tuple(
        sum(1 << column for column in columns)
        for columns in combinations(range(N), count)
    )


def advance_layer(
    layer: dict[FrontierState, PathNode], masks: tuple[int, ...]
) -> tuple[dict[FrontierState, PathNode], int]:
    outgoing: dict[FrontierState, PathNode] = {}
    live = 0
    for parent in layer.values():
        for mask in masks:
            child = advance_row(parent.state, mask)
            if child is None:
                continue
            live += 1
            _add_candidate(outgoing, child, parent, mask)
    return outgoing, live


def accepted_layer(
    layer: dict[FrontierState, PathNode],
) -> dict[FrontierState, PathNode]:
    accepted = {}
    for state, node in layer.items():
        if state.u_cost != TARGET_U:
            continue
        rows = _reconstruct(node)
        if dual_connectivity_check(rows)[0] and forest_completion_check(rows)[0]:
            accepted[state] = node
    return accepted


def fixed_cap_search(
    corridor: dict[FrontierState, PathNode],
) -> tuple[dict, list[str] | None]:
    layer = corridor
    rows = []
    for row in (18, 19):
        incoming_assignments = sum(node.ways for node in layer.values())
        incoming = len(layer)
        layer, live = advance_layer(layer, (row_mask(KNOWN_250[row]),))
        rows.append(
            {
                "row": row,
                "incoming_states": incoming,
                "assignments_attempted": incoming_assignments,
                "live_transitions": live,
                "outgoing_states": len(layer),
                "assignments_represented": sum(node.ways for node in layer.values()),
                "frontier_sha256": frontier_sha256(layer),
            }
        )
    accepted = accepted_layer(layer)
    witness = _reconstruct(next(iter(accepted.values()))) if accepted else None
    return {
        "result": "positive" if accepted else "negative",
        "rows": rows,
        "final_states": len(layer),
        "accepted_states": len(accepted),
        "accepted_assignments": sum(node.ways for node in accepted.values()),
    }, witness


def alternate_cap_search(
    corridor: dict[FrontierState, PathNode], report: bool
) -> tuple[list[CapStats], list[str] | None]:
    results = []
    witness = None
    for row18_u, row19_u in DISTRIBUTIONS:
        masks18 = masks_with_u_count(row18_u)
        row18, live18 = advance_layer(corridor, masks18)
        masks19 = masks_with_u_count(row19_u)
        row19, live19 = advance_layer(row18, masks19)
        accepted = accepted_layer(row19)
        if witness is None and accepted:
            witness = _reconstruct(next(iter(accepted.values())))
        stats = CapStats(
            row18_u,
            row19_u,
            len(masks18),
            len(corridor) * len(masks18),
            live18,
            len(row18),
            sum(node.ways for node in row18.values()),
            frontier_sha256(row18),
            len(masks19),
            len(row18) * len(masks19),
            live19,
            len(row19),
            sum(node.ways for node in row19.values()),
            frontier_sha256(row19),
            len(accepted),
            sum(node.ways for node in accepted.values()),
        )
        results.append(stats)
        if report:
            print(
                f"cap=({row18_u},{row19_u}) row18_states={len(row18)} "
                f"row18_assignments={stats.row18_assignments} row19_states={len(row19)} "
                f"row19_assignments={stats.row19_assignments} "
                f"accepted_assignments={stats.accepted_assignments}",
                flush=True,
            )
    return results, witness


def scope() -> dict:
    return {
        "base": "search_residue_two_middle.KNOWN_250",
        "n": N,
        "target_u": TARGET_U,
        "fixed_rows_primary_search": [[0, 10], [18, 19]],
        "mutable_rows": [FIRST_MUTABLE_ROW, LAST_MUTABLE_ROW],
        "mutable_packet_columns": list(MUTABLE_PACKET_COLUMNS),
        "mutable_packets": MUTABLE_PACKETS,
        "packet_count_per_row": PACKET_COUNT,
        "alphabet": list(BASIC_ALPHABET),
        "fixed_u_primary_search": FIXED_U,
        "required_h_packets_primary_search": REQUIRED_H_PACKETS,
        "charge_feasible_assignments_before_topology": CHARGE_FEASIBLE_ASSIGNMENTS,
        "alternate_cap_distributions": [list(value) for value in DISTRIBUTIONS],
        "deduplication_key": "full FrontierState",
        "exact_multiplicities": True,
        "beam": None,
        "state_cap": None,
        "partition_projection": None,
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

    completed_rows: list[dict] = []

    def checkpoint(stats: RowStats, layer: dict[FrontierState, PathNode]) -> None:
        completed_rows.append({**asdict(stats), "frontier_sha256": frontier_sha256(layer)})

    record = {
        "schema": "grid-graphs.residue-two-suffix-corridor-21.v1",
        "exact": False,
        "provenance": provenance(),
        "scope": scope(),
        "result": "incomplete",
        "completed_corridor_rows": completed_rows,
        "fixed_cap": None,
        "alternate_caps": None,
        "witness": None,
    }
    previous_handler = signal.signal(signal.SIGALRM, _timeout)
    signal.alarm(args.max_seconds)
    try:
        corridor, _ = layer_after_row17(
            report=not args.quiet,
            mutable_packet_columns=MUTABLE_PACKET_COLUMNS,
            on_layer=checkpoint,
        )
        record["corridor_after_row17"] = {
            "states": len(corridor),
            "assignments": sum(node.ways for node in corridor.values()),
            "frontier_sha256": frontier_sha256(corridor),
        }
        fixed, witness = fixed_cap_search(corridor)
        record["fixed_cap"] = fixed
        if fixed["result"] == "negative":
            caps, cap_witness = alternate_cap_search(corridor, not args.quiet)
            record["alternate_caps"] = [asdict(stats) for stats in caps]
            witness = cap_witness
        record["exact"] = True
        record["result"] = "positive" if witness is not None else "negative"
        record["witness"] = witness
    except TimeoutError:
        record["stop_reason"] = f"time limit reached after {args.max_seconds} seconds"
    finally:
        signal.alarm(0)
        signal.signal(signal.SIGALRM, previous_handler)

    args.certificate.write_text(json.dumps(record, indent=2) + "\n")
    if not record["exact"]:
        print(
            f"INCOMPLETE: exhausted rows {[row['row'] for row in completed_rows]}; "
            "no exact negative is claimed."
        )
        print(f"certificate={args.certificate}")
        raise SystemExit(2)
    if record["witness"] is not None:
        info = run_check(N, record["witness"], verbose=not args.quiet)
        if not info["all_ok"]:
            raise AssertionError(f"independent run_check rejected witness: {info}")
        args.witness.write_text("\n".join(record["witness"]) + "\n")
        print("EXACT POSITIVE")
        print(f"witness={args.witness}")
    else:
        print("EXACT NEGATIVE in the primary and three declared alternate cap scopes.")
    print(f"certificate={args.certificate}")


if __name__ == "__main__":
    main()
