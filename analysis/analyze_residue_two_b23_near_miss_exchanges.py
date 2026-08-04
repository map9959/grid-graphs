#!/usr/bin/env python3
"""Test equal-count bridge exchanges in the exact best 333-U near misses."""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path

from construction_lab import dual_connectivity_check, forest_completion_check


HERE = Path(__file__).resolve().parent
INPUT = HERE / "residue_two_b20_to_b23_basic_result.json"
DEFAULT_OUTPUT = HERE / "residue_two_b23_near_miss_exchanges.json"
MUTABLE_ROWS = range(6, 17)


def toggle(rows: list[str], additions=(), removals=()) -> list[str]:
    materialized = [list(row) for row in rows]
    for row, col in additions:
        materialized[row][col] = "U"
    for row, col in removals:
        materialized[row][col] = "."
    return ["".join(row) for row in materialized]


def analyze_example(example: dict) -> dict:
    rows = example["rows"]
    additions = sorted({
        tuple(edge["needed_u_cells"][0])
        for edge in example["dual"]["missing_cut_edges"]
        if edge["additions"] == 1 and edge["needed_u_cells"][0][0] in MUTABLE_ROWS
    })
    removals = [
        (row, col)
        for row in MUTABLE_ROWS
        for col, value in enumerate(rows[row])
        if value == "U"
    ]
    by_size = {}
    witnesses = []
    for size in (1, 2):
        connected_additions = 0
        first_removals_tested = 0
        connected_first_removals = 0
        final_removals_tested = 0
        for added in itertools.combinations(additions, size):
            augmented = toggle(rows, additions=added)
            if not dual_connectivity_check(augmented)[0]:
                continue
            connected_additions += 1
            if size == 1:
                removal_sets = ((removed,) for removed in removals)
            else:
                first = []
                for removed in removals:
                    first_removals_tested += 1
                    once = toggle(augmented, removals=(removed,))
                    if dual_connectivity_check(once)[0]:
                        connected_first_removals += 1
                        first.append(removed)
                removal_sets = (
                    pair
                    for removed in first
                    for pair in itertools.combinations(removals, 2)
                    if removed in pair
                )
            seen = set()
            for removed in removal_sets:
                removed = tuple(sorted(removed))
                if removed in seen:
                    continue
                seen.add(removed)
                final_removals_tested += 1
                candidate = toggle(augmented, removals=removed)
                if not dual_connectivity_check(candidate)[0]:
                    continue
                forest_ok, reason = forest_completion_check(candidate)
                witnesses.append({
                    "additions": added,
                    "removals": removed,
                    "forest_ok": forest_ok,
                    "forest_reason": reason,
                    "rows": candidate,
                })
        by_size[str(size)] = {
            "addition_sets": sum(1 for _ in itertools.combinations(additions, size)),
            "connected_after_additions": connected_additions,
            "first_removals_tested": first_removals_tested,
            "connected_first_removals": connected_first_removals,
            "final_removals_tested": final_removals_tested,
        }
    return {
        "source_sha256": example["sha256"],
        "candidate_addition_cells": additions,
        "candidate_removal_cells": len(removals),
        "by_exchange_size": by_size,
        "witnesses": witnesses,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()
    source = json.loads(INPUT.read_text())
    examples = source["budgets"]["333"]["best_examples"]
    record = {
        "schema": "grid-graphs.residue-two-b23-near-miss-exchanges.v1",
        "scope": (
            "All one-for-one and two-for-two exchanges whose additions are one-cell "
            "bridges of an original component cut and whose changed cells lie in "
            "mutable rows 6..16."
        ),
        "examples": [analyze_example(example) for example in examples],
    }
    record["witness_count"] = sum(len(item["witnesses"]) for item in record["examples"])
    args.output.write_text(json.dumps(record, indent=2) + "\n")
    print(f"wrote {args.output}: witnesses={record['witness_count']}")


if __name__ == "__main__":
    main()
