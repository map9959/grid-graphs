#!/usr/bin/env python3
"""Exact attachment-debt histories from committed residue-two witnesses.

This is deliberately a replay/analyzer, not a frontier search.  A rooted
attachment debt is the number of live dual components not containing OUT.
Merge capacity on the terminal suffix is computed by exhaustive transition
enumeration under the stated U budget.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

from analysis.patterns.diagonal_patterns import residue_two_explicit_pattern
from analysis._paths import ANALYSIS_ROOT


HERE = ANALYSIS_ROOT
SURVIVORS = HERE / "frontier_n17_u178_step287.json"
REPLAY_179 = HERE / "frontier_n17_u179_replay.json"
WITNESS_179 = HERE / "residue_two_affine_17_witness.txt"
DEFAULT_OUTPUT = HERE / "residue_two_attachment_history.json"
SCHEMA = "grid-graphs.residue-two-attachment-history.v1"


@dataclass(frozen=True)
class Frontier:
    completed_steps: int
    labels: tuple[int, ...]
    row_u: int
    cost: int

    @property
    def rooted_debt(self) -> int:
        root = self.labels[0]
        return len(set(self.labels) - {root})


class Dsu:
    def __init__(self, size: int):
        self.parent = list(range(size))

    def root(self, item: int) -> int:
        while self.parent[item] != item:
            self.parent[item] = self.parent[self.parent[item]]
            item = self.parent[item]
        return item

    def join(self, left: int, right: int) -> bool:
        left, right = self.root(left), self.root(right)
        if left == right:
            return False
        self.parent[right] = left
        return True


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _canonical(values: Iterable[int]) -> tuple[int, ...]:
    names: dict[int, int] = {}
    return tuple(names.setdefault(value, len(names)) for value in values)


def _face(n: int, row: int, col: int) -> int:
    return row * (n - 1) + col


def _bags(n: int, at: int) -> tuple[list[int], list[int], list[int]]:
    """Return before/work/after dual-node bags for one row-major cell."""
    face_count = (n - 1) ** 2
    out = face_count
    first = [10**9] * face_count
    last = [-1] * face_count
    batches: list[list[tuple[int, int, str]]] = [[] for _ in range(n * n)]
    for row in range(n):
        for col in range(n):
            edges = batches[row * n + col]
            if col:
                edges.append(
                    (
                        out if row == 0 else _face(n, row - 1, col - 1),
                        out if row + 1 == n else _face(n, row, col - 1),
                        "left",
                    )
                )
            if row:
                edges.append(
                    (
                        out if col == 0 else _face(n, row - 1, col - 1),
                        out if col + 1 == n else _face(n, row - 1, col),
                        "up",
                    )
                )
            for left, right, _ in edges:
                for node in (left, right):
                    if node != out:
                        first[node] = min(first[node], row * n + col)
                        last[node] = max(last[node], row * n + col)
    before = [out, *(node for node in range(face_count) if first[node] < at <= last[node])]
    after = [out, *(node for node in range(face_count) if first[node] <= at < last[node])]
    work = list(before)
    for edge in batches[at]:
        for node in edge[:2]:
            if node not in work:
                work.append(node)
    return before, work, after


def _edges(n: int, at: int) -> list[tuple[int, int, str]]:
    row, col = divmod(at, n)
    out = (n - 1) ** 2
    edges = []
    if col:
        edges.append(
            (
                out if row == 0 else _face(n, row - 1, col - 1),
                out if row + 1 == n else _face(n, row, col - 1),
                "left",
            )
        )
    if row:
        edges.append(
            (
                out if col == 0 else _face(n, row - 1, col - 1),
                out if col + 1 == n else _face(n, row - 1, col),
                "up",
            )
        )
    return edges


def advance_cell(n: int, state: Frontier, chosen: bool) -> tuple[Frontier | None, dict]:
    """Apply the exact Rust frontier transition and return local merge facts."""
    at = state.completed_steps
    row, col = divmod(at, n)
    before, work, after = _bags(n, at)
    if len(before) != len(state.labels):
        raise ValueError("frontier label count does not match the schedule")
    positions = {node: index for index, node in enumerate(work)}
    dsu = Dsu(len(work))
    for left in range(len(before)):
        for right in range(left):
            if state.labels[left] == state.labels[right]:
                dsu.join(left, right)

    matched = 0
    active = []
    independent_merges = 0
    for left, right, kind in _edges(n, at):
        neighbor = col > 0 and state.row_u & (1 << (col - 1)) if kind == "left" else row > 0 and state.row_u & (1 << col)
        bit = 1 if kind == "left" else 2
        if chosen and neighbor:
            matched |= bit
            active.append(kind)
            independent_merges += dsu.join(positions[left], positions[right])

    represented = {dsu.root(positions[node]) for node in after}
    retired = any(dsu.root(index) not in represented for index in range(len(work)))
    facts = {
        "matched_neighbor_mask": matched,
        "matched_neighbors": active,
        "independent_edge_merges": independent_merges,
        "retired_component": retired,
    }
    if retired:
        return None, facts
    labels = _canonical(dsu.root(positions[node]) for node in after)
    row_u = state.row_u | (1 << col) if chosen else state.row_u & ~(1 << col)
    return Frontier(at + 1, labels, row_u, state.cost + int(chosen)), facts


def row_mask(row: str) -> int:
    return sum((cell == "U") << col for col, cell in enumerate(row))


def replay_rows(rows: list[str]) -> list[dict]:
    """Replay a witness and return every exact row-boundary debt state."""
    n = len(rows)
    state = Frontier(0, (0,), 0, 0)
    history = [{"completed_rows": 0, "u_cost": 0, "components": 1, "rooted_debt": 0}]
    for row_index, row in enumerate(rows):
        merges = 0
        matched_edges = 0
        for col, cell in enumerate(row):
            state, facts = advance_cell(n, state, cell == "U")
            if state is None:
                raise ValueError(f"witness retires a component at {(row_index, col)}")
            merges += facts["independent_edge_merges"]
            matched_edges += len(facts["matched_neighbors"])
        history.append(
            {
                "completed_rows": row_index + 1,
                "row_u_mask": row_mask(row),
                "row_u_bits_col0_first": row,
                "u_cost": state.cost,
                "components": len(set(state.labels)),
                "rooted_debt": state.rooted_debt,
                "active_dual_edges_in_row": matched_edges,
                "independent_merges_in_row": merges,
            }
        )
    if state.labels != (0,) or state.rooted_debt:
        raise ValueError("witness does not finish connected")
    return history


def suffix_capacity(n: int, state: Frontier, target: int) -> dict:
    """Exhaust the remaining suffix and maximize independent component merges."""
    start_debt = state.rooted_debt
    outcomes: list[dict] = []

    def visit(current: Frontier, choices: list[bool], merges: int, masks: list[int]) -> None:
        if current.completed_steps == n * n:
            outcomes.append(
                {
                    "choices": choices,
                    "merges": merges,
                    "matched_neighbor_masks": masks,
                    "accepted": current.labels == (0,),
                    "final_debt": current.rooted_debt,
                }
            )
            return
        attempted = False
        for chosen in (False, True):
            if current.cost + int(chosen) > target:
                continue
            attempted = True
            following, facts = advance_cell(n, current, chosen)
            if following is None:
                outcomes.append(
                    {
                        "choices": [*choices, chosen],
                        "merges": merges + facts["independent_edge_merges"],
                        "matched_neighbor_masks": [*masks, facts["matched_neighbor_mask"]],
                        "accepted": False,
                        "failure": "retired_component",
                    }
                )
            else:
                visit(
                    following,
                    [*choices, chosen],
                    merges + facts["independent_edge_merges"],
                    [*masks, facts["matched_neighbor_mask"]],
                )
        if not attempted:
            outcomes.append({"choices": choices, "merges": merges, "accepted": False, "failure": "budget"})

    visit(state, [], 0, [])
    return {
        "rooted_debt": start_debt,
        "remaining_u_budget": target - state.cost,
        "budgeted_merge_capacity": max(item["merges"] for item in outcomes),
        "accepted_suffix_count": sum(item["accepted"] for item in outcomes),
        "suffix_outcomes": outcomes,
    }


def _load_witness_179() -> list[str]:
    return [line for line in WITNESS_179.read_text().splitlines() if not line.startswith("#")]


def build_analysis() -> dict:
    dump = json.loads(SURVIVORS.read_text())
    replay = json.loads(REPLAY_179.read_text())
    survivor_records = []
    for item in dump["states"]:
        state = Frontier(dump["completed_steps"], tuple(item["labels"]), item["row_u"], item["cost"])
        survivor_records.append(
            {
                "packed_state": item["packed_state"],
                "cost": item["cost"],
                "row_u": item["row_u"],
                "row_bits_col0_first": item["row_bits_col0_first"],
                **suffix_capacity(17, state, dump["target"]),
            }
        )

    final_record = next(item for item in replay["records"] if item["completed_steps"] == 287)
    witness_state = Frontier(287, tuple(final_record["labels"]), final_record["row_u"], final_record["cost"])
    witnesses = {n: residue_two_explicit_pattern(n) for n in (5, 8, 11, 14)}
    witnesses[17] = _load_witness_179()
    witness_histories = {
        str(n): {
            "n": n,
            "u_count": sum(row.count("U") for row in rows),
            "rows_sha256": hashlib.sha256(("\n".join(rows) + "\n").encode()).hexdigest(),
            "row_boundaries": replay_rows(rows),
        }
        for n, rows in witnesses.items()
    }
    capacity_counts: dict[str, int] = {}
    for state in survivor_records:
        key = str(state["budgeted_merge_capacity"])
        capacity_counts[key] = capacity_counts.get(key, 0) + 1

    return {
        "schema": SCHEMA,
        "definition": {
            "rooted_attachment_debt": "number of live dual components not containing OUT",
            "independent_edge_merge": "an active dual edge whose endpoints were in distinct components when applied",
            "budgeted_merge_capacity": "maximum independent edge merges over every remaining cell choice sequence within the U budget; exact suffix enumeration",
            "matched_neighbor_mask": "bit 0 = chosen cell has a U left neighbor; bit 1 = chosen cell has a U upper neighbor",
        },
        "provenance": {
            SURVIVORS.name: _sha256(SURVIVORS),
            REPLAY_179.name: _sha256(REPLAY_179),
            WITNESS_179.name: _sha256(WITNESS_179),
        },
        "terminal_178": {
            "completed_steps": 287,
            "state_count": len(survivor_records),
            "capacity_counts": capacity_counts,
            "states": survivor_records,
        },
        "witness_179_suffix": {
            "completed_steps": 287,
            "packed_state": final_record["packed_state"],
            **suffix_capacity(17, witness_state, replay["u_count"]),
        },
        "explicit_witness_histories": witness_histories,
        "limitations": [
            "The committed 178-U step-287 dump stores states and minimum costs, but no predecessor identities, backpointers, or prefix patterns.",
            "Therefore no row-boundary prefix history can be assigned to any of the 20 terminal survivors from committed data; only their exact remaining two-cell suffixes are reconstructible.",
            "The 179-U replay stores row boundaries and the final four steps, while its committed explicit pattern makes its complete cell and row history exactly replayable.",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true", help="compare exact regeneration with the cached JSON")
    args = parser.parse_args()
    analysis = build_analysis()
    text = json.dumps(analysis, indent=2, sort_keys=True) + "\n"
    if args.check:
        if not args.output.exists() or args.output.read_text() != text:
            raise SystemExit(f"stale or missing artifact: {args.output}")
        print(f"exact attachment history matches {args.output}")
    else:
        args.output.write_text(text)
        print(f"wrote {args.output}")


if __name__ == "__main__":
    main()
