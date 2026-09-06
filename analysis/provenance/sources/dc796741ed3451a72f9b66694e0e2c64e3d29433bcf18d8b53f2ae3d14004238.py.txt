#!/usr/bin/env python3
"""Exhaust the n=20, 14-packet suffix corridor around ``KNOWN_250``.

Rows 0..10 and 18..19 are fixed.  In rows 11..17, packet columns 0 and 1
range over L/X/R/H while every other bit remains fixed to ``KNOWN_250``.
The frontier search is exact: it has no beam, cap, or projected partition.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import asdict, dataclass
from math import comb
from pathlib import Path
from typing import Callable

from construction_lab import (
    dual_connectivity_check,
    forest_completion_check,
    q_old_formula as q_formula,
    run_check,
)
from search_residue_two_middle import BASIC_ALPHABET, KNOWN_250
from tile_grammar import (
    FrontierState,
    advance_row,
    initial_state,
    render_mask,
    row_mask,
    stream_row_packets,
)


N = 20
TARGET_U = 249
FIRST_MUTABLE_ROW = 11
LAST_MUTABLE_ROW = 17
MUTABLE_PACKET_COLUMNS = (0, 1)
PACKET_COUNT = 6
PACKET_WIDTH = 3
FIXED_U = 215
REQUIRED_H_PACKETS = 6
CHARGE_FEASIBLE_ASSIGNMENTS = comb(14, REQUIRED_H_PACKETS) * 3 ** (14 - REQUIRED_H_PACKETS)
DEFAULT_WITNESS = Path(__file__).with_name("residue_two_suffix_corridor_witness.txt")
DEFAULT_CERTIFICATE = Path(__file__).with_name("residue_two_suffix_corridor_result.json")


def _sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def known_250_sha256() -> str:
    """Hash the exact row payload, including separators and final newline."""

    return _sha256_bytes(("\n".join(KNOWN_250) + "\n").encode("ascii"))


def provenance() -> dict:
    directory = Path(__file__).parent
    paths = {
        "generator": Path(__file__),
        "base_pattern_source": directory / "search_residue_two_middle.py",
        "frontier_kernel": directory / "tile_grammar.py",
    }
    return {
        "known_250_rows_sha256": known_250_sha256(),
        "source_files": {
            name: {"path": path.name, "sha256": _sha256_bytes(path.read_bytes())}
            for name, path in paths.items()
        },
    }


@dataclass(frozen=True, slots=True)
class PathNode:
    """One exact frontier state, one sound predecessor, and path multiplicity."""

    state: FrontierState
    ways: int
    parent: PathNode | None
    row_mask: int | None
    packet_names: tuple[str, ...] = ()


@dataclass(frozen=True, slots=True)
class RowStats:
    row: int
    incoming_states: int
    packet_extensions: int
    viable_transitions: int
    outgoing_states: int
    assignments_represented: int


@dataclass(frozen=True, slots=True)
class SearchResult:
    witness: list[str] | None
    stats: list[RowStats]
    accepted_states: int
    accepted_assignments: int
    final_states: int

    @property
    def found(self) -> bool:
        return self.witness is not None


def exact_state_key(state: FrontierState) -> FrontierState:
    """Use every frontier field, notably the full unprojected partition."""

    return state


def _packet_name(value: str) -> str:
    matches = [name for name, packet in BASIC_ALPHABET.items() if packet == value]
    if len(matches) != 1:
        raise ValueError(f"fixed packet {value!r} is not uniquely in the basic alphabet")
    return matches[0]


def packet_domains(
    row: int,
    variable: bool = True,
    mutable_packet_columns: tuple[int, ...] = MUTABLE_PACKET_COLUMNS,
) -> tuple[tuple[str, ...], ...]:
    """Return the six packet domains for one declared corridor row."""

    if not FIRST_MUTABLE_ROW <= row <= LAST_MUTABLE_ROW:
        raise ValueError("row is outside the declared corridor")
    domains = []
    for packet_column in range(PACKET_COUNT):
        value = KNOWN_250[row][1 + PACKET_WIDTH * packet_column : 4 + PACKET_WIDTH * packet_column]
        fixed_name = _packet_name(value)
        if variable and packet_column in mutable_packet_columns:
            domains.append(tuple(BASIC_ALPHABET))
        else:
            domains.append((fixed_name,))
    return tuple(domains)


def fixed_u_for(mutable_packet_columns: tuple[int, ...]) -> int:
    """Return the contribution of every bit outside the mutable packets."""

    mutable = sum(
        KNOWN_250[row][1 + PACKET_WIDTH * column : 4 + PACKET_WIDTH * column].count("U")
        for row in range(FIRST_MUTABLE_ROW, LAST_MUTABLE_ROW + 1)
        for column in mutable_packet_columns
    )
    return sum(row.count("U") for row in KNOWN_250) - mutable


def validate_scope(
    mutable_packet_columns: tuple[int, ...] = MUTABLE_PACKET_COLUMNS,
) -> None:
    if len(KNOWN_250) != N or any(len(row) != N for row in KNOWN_250):
        raise ValueError("KNOWN_250 must be a 20x20 pattern")
    if set(BASIC_ALPHABET) != {"L", "X", "R", "H"}:
        raise ValueError("basic packet alphabet is not L/X/R/H")
    if len(set(mutable_packet_columns)) != len(mutable_packet_columns) or any(
        not 0 <= column < PACKET_COUNT for column in mutable_packet_columns
    ):
        raise ValueError("mutable packet columns must be unique columns in the row grammar")
    for row in range(FIRST_MUTABLE_ROW, LAST_MUTABLE_ROW + 1):
        if KNOWN_250[row][0] != "." or KNOWN_250[row][-1] != ".":
            raise ValueError("corridor row boundary differs from the packet grammar")
        packet_domains(row, mutable_packet_columns=mutable_packet_columns)
    fixed_u = fixed_u_for(mutable_packet_columns)
    if mutable_packet_columns == MUTABLE_PACKET_COLUMNS and fixed_u != FIXED_U:
        raise AssertionError(f"fixed corridor contribution changed: {fixed_u}")
    if q_formula(N) != TARGET_U:
        raise AssertionError("n=20 target formula changed")


def _future_u_bounds(
    after_row: int,
    variable: bool,
    mutable_packet_columns: tuple[int, ...] = MUTABLE_PACKET_COLUMNS,
) -> tuple[int, int]:
    minimum = maximum = sum(
        KNOWN_250[row].count("U") for row in range(after_row + 1, N)
    )
    for row in range(max(after_row + 1, FIRST_MUTABLE_ROW), LAST_MUTABLE_ROW + 1):
        # Replace the known mutable packets included in the sum above.
        known = sum(
            KNOWN_250[row][1 + 3 * column : 4 + 3 * column].count("U")
            for column in mutable_packet_columns
        )
        minimum -= known
        maximum -= known
        if variable:
            minimum += 2 * len(mutable_packet_columns)
            maximum += 3 * len(mutable_packet_columns)
        else:
            minimum += known
            maximum += known
    return minimum, maximum


def _add_candidate(
    candidates: dict[FrontierState, PathNode],
    state: FrontierState,
    parent: PathNode,
    mask: int,
    packet_names: tuple[str, ...] = (),
) -> None:
    key = exact_state_key(state)
    old = candidates.get(key)
    if old is None:
        candidates[key] = PathNode(state, parent.ways, parent, mask, packet_names)
    else:
        # Keep the old valid predecessor while exactly aggregating represented paths.
        candidates[key] = PathNode(state, old.ways + parent.ways, old.parent, old.row_mask, old.packet_names)


def _reconstruct(node: PathNode) -> list[str]:
    masks = []
    while node.parent is not None:
        if node.row_mask is None:
            raise AssertionError("non-root predecessor has no row mask")
        masks.append(node.row_mask)
        node = node.parent
    masks.reverse()
    if len(masks) != N:
        raise AssertionError(f"predecessor chain has {len(masks)} rows, expected {N}")
    return [render_mask(mask, N) for mask in masks]


def layer_after_row17(
    *,
    target_u: int = TARGET_U,
    variable: bool = True,
    report: bool = True,
    mutable_packet_columns: tuple[int, ...] = MUTABLE_PACKET_COLUMNS,
    on_layer: Callable[[RowStats, dict[FrontierState, PathNode]], None] | None = None,
) -> tuple[dict[FrontierState, PathNode], list[RowStats]]:
    """Return every exact corridor state after row 17 with predecessors and ways."""

    validate_scope(mutable_packet_columns)
    state = initial_state(N)
    root = PathNode(state, 1, None, None)
    node = root
    for row in range(FIRST_MUTABLE_ROW):
        child = advance_row(node.state, row_mask(KNOWN_250[row]))
        if child is None:
            raise AssertionError(f"fixed prefix seals a dual component at row {row}")
        node = PathNode(child, 1, node, row_mask(KNOWN_250[row]))

    layer = {exact_state_key(node.state): node}
    stats = []
    for row in range(FIRST_MUTABLE_ROW, LAST_MUTABLE_ROW + 1):
        incoming_states = len(layer)
        future_min, future_max = _future_u_bounds(row, variable, mutable_packet_columns)
        candidates: dict[FrontierState, PathNode] = {}
        packet_extensions = 0
        viable_transitions = 0
        for parent in layer.values():
            transitions, attempted = stream_row_packets(
                parent.state,
                ".",
                ".",
                packet_domains(row, variable, mutable_packet_columns),
                packet_alphabet=BASIC_ALPHABET,
                u_cost_bounds=(target_u - future_max, target_u - future_min),
            )
            packet_extensions += attempted
            viable_transitions += len(transitions)
            for transition in transitions:
                _add_candidate(
                    candidates,
                    transition.outgoing,
                    parent,
                    transition.row_mask,
                    transition.packet_names,
                )
        layer = candidates
        row_stats = RowStats(
            row,
            incoming_states=incoming_states,
            packet_extensions=packet_extensions,
            viable_transitions=viable_transitions,
            outgoing_states=len(layer),
            assignments_represented=sum(child.ways for child in layer.values()),
        )
        stats.append(row_stats)
        if on_layer is not None:
            on_layer(row_stats, layer)
        if report:
            print(
                f"row={row} incoming_states={row_stats.incoming_states} "
                f"packet_extensions={packet_extensions} viable_transitions={viable_transitions} "
                f"outgoing_states={len(layer)} assignments={row_stats.assignments_represented}",
                flush=True,
            )

    return layer, stats


def search(
    *,
    target_u: int = TARGET_U,
    variable: bool = True,
    report: bool = True,
    mutable_packet_columns: tuple[int, ...] = MUTABLE_PACKET_COLUMNS,
) -> SearchResult:
    """Exhaust the declared domains and return an independently checked witness."""

    layer, stats = layer_after_row17(
        target_u=target_u,
        variable=variable,
        report=report,
        mutable_packet_columns=mutable_packet_columns,
    )

    for row in range(LAST_MUTABLE_ROW + 1, N):
        incoming_states = len(layer)
        candidates = {}
        viable_transitions = 0
        mask = row_mask(KNOWN_250[row])
        for parent in layer.values():
            child = advance_row(parent.state, mask)
            if child is None or (row + 1 == N and child.u_cost != target_u):
                continue
            viable_transitions += 1
            _add_candidate(candidates, child, parent, mask)
        layer = candidates
        row_stats = RowStats(
            row,
            incoming_states,
            incoming_states,
            viable_transitions,
            len(layer),
            sum(child.ways for child in layer.values()),
        )
        stats.append(row_stats)
        if report:
            print(
                f"row={row} fixed_transitions={incoming_states} viable_transitions={viable_transitions} "
                f"outgoing_states={len(layer)} assignments={row_stats.assignments_represented}",
                flush=True,
            )

    accepted_states = 0
    accepted_assignments = 0
    witness = None
    for final in layer.values():
        rows = _reconstruct(final)
        dual_ok, _, _ = dual_connectivity_check(rows)
        forest_ok, _ = forest_completion_check(rows)
        if not dual_ok or not forest_ok:
            continue
        accepted_states += 1
        accepted_assignments += final.ways
        if witness is None:
            witness = rows
    return SearchResult(witness, stats, accepted_states, accepted_assignments, len(layer))


def certificate(result: SearchResult) -> dict:
    return {
        "schema": "grid-graphs.residue-two-suffix-corridor.v1",
        "exact": True,
        "provenance": provenance(),
        "scope": {
            "base": "search_residue_two_middle.KNOWN_250",
            "n": N,
            "target_u": TARGET_U,
            "fixed_rows": [[0, 10], [18, 19]],
            "mutable_rows": [FIRST_MUTABLE_ROW, LAST_MUTABLE_ROW],
            "mutable_packet_columns": list(MUTABLE_PACKET_COLUMNS),
            "mutable_packets": 14,
            "alphabet": list(BASIC_ALPHABET),
            "fixed_u": FIXED_U,
            "required_h_packets": REQUIRED_H_PACKETS,
            "charge_feasible_assignments_before_topology": CHARGE_FEASIBLE_ASSIGNMENTS,
            "beam_or_state_cap": None,
            "partition_projection": None,
        },
        "result": "positive" if result.found else "negative",
        "final_states": result.final_states,
        "accepted_states": result.accepted_states,
        "accepted_assignments": result.accepted_assignments,
        "rows": [asdict(row) for row in result.stats],
        "witness": result.witness,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--quiet", action="store_true", help="suppress per-row progress")
    parser.add_argument("--witness", type=Path, default=DEFAULT_WITNESS)
    parser.add_argument("--certificate", type=Path, default=DEFAULT_CERTIFICATE)
    args = parser.parse_args()

    result = search(report=not args.quiet)
    record = certificate(result)
    args.certificate.write_text(json.dumps(record, indent=2) + "\n")
    if result.witness is None:
        print(
            "EXACT NEGATIVE: no dual-connected and forest-completable U=249 pattern "
            "in rows 11..17 x packet columns 0..1 over L/X/R/H, with every other "
            "packet and rows 0..10,18..19 fixed to KNOWN_250."
        )
        print(f"certificate={args.certificate}")
        raise SystemExit(1)

    info = run_check(N, result.witness, verbose=True)
    if not info["all_ok"]:
        raise AssertionError(f"independent run_check rejected witness: {info}")
    args.witness.write_text("\n".join(result.witness) + "\n")
    print(
        f"EXACT POSITIVE: accepted_states={result.accepted_states} "
        f"accepted_assignments={result.accepted_assignments}"
    )
    print("\n".join(result.witness))
    print(f"witness={args.witness}")
    print(f"certificate={args.certificate}")


if __name__ == "__main__":
    main()
