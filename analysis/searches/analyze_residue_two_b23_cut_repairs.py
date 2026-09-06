#!/usr/bin/env python3
"""Exact cut-directed exchanges in the best 333-U n=23 near misses.

This is a bounded local repair analysis, not a global n=23 search.  An allowed
addition set has size at most three and is the union of at most three complete
endpoint deficits of dual edges crossing an original component cut.  Balancing
removals may be any original U cell on the board.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from collections import Counter
from pathlib import Path

from analysis.patterns.construction_lab import dual_connectivity_check, forest_completion_check
from analysis.searches.search_residue_two_target_control import ConnectivitySensitivity, changed_rows
from analysis._paths import ANALYSIS_ROOT


HERE = ANALYSIS_ROOT
INPUT = HERE / "residue_two_b20_to_b23_basic_result.json"
DEFAULT_OUTPUT = HERE / "residue_two_b23_cut_repairs.json"
SCHEMA = "grid-graphs.residue-two-b23-cut-repairs.v1"


def rows_sha256(rows: list[str]) -> str:
    return hashlib.sha256(("\n".join(rows) + "\n").encode("ascii")).hexdigest()


def cut_deficits(example: dict) -> tuple[frozenset[tuple[int, int]], ...]:
    return tuple(sorted(
        {
            frozenset(map(tuple, edge["needed_u_cells"]))
            for edge in example["dual"]["missing_cut_edges"]
        },
        key=lambda cells: tuple(sorted(cells)),
    ))


def addition_sets(
    deficits: tuple[frozenset[tuple[int, int]], ...], order: int
) -> tuple[tuple[tuple[int, int], ...], ...]:
    result = set()
    for deficit_count in range(1, 4):
        for selected in itertools.combinations(deficits, deficit_count):
            cells = frozenset().union(*selected)
            if len(cells) == order:
                result.add(tuple(sorted(cells)))
    return tuple(sorted(result))


def analyze_example(example: dict) -> dict:
    rows = example["rows"]
    if sum(row.count("U") for row in rows) != 333:
        raise AssertionError("source is not an exact 333-U pattern")
    if dual_connectivity_check(rows)[0]:
        raise AssertionError("source unexpectedly became dual-connected")

    deficits = cut_deficits(example)
    sensitivity = ConnectivitySensitivity(rows)
    orders = []
    for order in (1, 2, 3):
        additions = addition_sets(deficits, order)
        connected_augmentations = 0
        removable_histogram: Counter[int] = Counter()
        final_tuples = 0
        connected_final = 0
        forest_final = 0
        final_replays = []
        for added in additions:
            augmented = changed_rows(rows, added, ())
            if not dual_connectivity_check(augmented)[0]:
                continue
            connected_augmentations += 1
            removable = sensitivity.individually_removable(added)
            removable_histogram[len(removable)] += 1
            for removed in itertools.combinations(removable, order):
                final_tuples += 1
                candidate = changed_rows(augmented, (), removed)
                dual = dual_connectivity_check(candidate)
                forest = forest_completion_check(candidate) if dual[0] else (False, "not checked")
                connected_final += dual[0]
                forest_final += forest[0]
                final_replays.append({
                    "additions": added,
                    "removals": removed,
                    "sha256": rows_sha256(candidate),
                    "dual_connected": dual[0],
                    "dual_reached": dual[1],
                    "dual_total": dual[2],
                    "forest_ok": forest[0],
                    "forest_reason": forest[1],
                })
        orders.append({
            "order": order,
            "addition_sets": len(additions),
            "connected_augmentations": connected_augmentations,
            "individually_removable_histogram": {
                str(count): frequency
                for count, frequency in sorted(removable_histogram.items())
            },
            "final_removal_tuples": final_tuples,
            "dual_connected_final": connected_final,
            "forest_completable_final": forest_final,
            "final_replays": final_replays,
        })
    return {
        "source_sha256": example["sha256"],
        "source_component_count": example["dual"]["component_count"],
        "distinct_cut_deficits": len(deficits),
        "deficit_size_histogram": {
            str(size): sum(len(deficit) == size for deficit in deficits)
            for size in (1, 2)
        },
        "orders": orders,
    }


def run() -> dict:
    source = json.loads(INPUT.read_text(encoding="ascii"))
    examples = [analyze_example(example) for example in source["budgets"]["333"]["best_examples"]]
    witnesses = sum(
        order["forest_completable_final"]
        for example in examples
        for order in example["orders"]
    )
    return {
        "schema": SCHEMA,
        "status": "SAT" if witnesses else "UNSAT_IN_DECLARED_CUT_REPAIR_NEIGHBORHOOD",
        "exact_in_declared_scope": True,
        "scope": {
            "sources": "the three best exact 333-U examples in residue_two_b20_to_b23_basic_result.json",
            "orders": [1, 2, 3],
            "addition_rule": (
                "An order-k addition is a k-cell union of at most three complete endpoint-deficit "
                "sets of dual edges crossing an original component cut."
            ),
            "removal_rule": "Any k original U cells on the 23x23 board; added cells are not removed.",
            "negative_claim": (
                "Only these cut-directed equal-count exchanges around the three listed sources are "
                "excluded. This is not a global n=23 impossibility result."
            ),
        },
        "method": {
            "augmentation_connectivity": "construction_lab.dual_connectivity_check",
            "exact_removal_prune": (
                "If deleting a set preserves connectivity, deleting each member alone preserves "
                "connectivity. ConnectivitySensitivity computes those singleton conditions exactly."
            ),
            "final_replay": (
                "Every unpruned equal-count tuple is independently materialized and checked with "
                "dual_connectivity_check and forest_completion_check."
            ),
        },
        "examples": examples,
        "witness_count": witnesses,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()
    result = run()
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="ascii")
    print(f"wrote {args.output}: {result['status']}")


if __name__ == "__main__":
    main()
