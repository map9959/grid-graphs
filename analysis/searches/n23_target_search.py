#!/usr/bin/env python3
"""Exact finite searches for a 333-U n=23 target construction.

The negative claims made here are only for the explicitly declared sources,
exchange orders, and spatial windows.  They are not a global n=23 census.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from collections import Counter
from math import comb
from pathlib import Path

from analysis._paths import ANALYSIS_ROOT
from analysis.patterns.construction_lab import (
    dual_connectivity_check,
    forest_completion_check,
)
from analysis.patterns.diagonal_patterns import residue_two_affine_pattern
from analysis.residue_certificates.residue_two_revised_recurrence import (
    target_charge_candidate,
)
from analysis.searches.search_residue_two_target_control import (
    ConnectivitySensitivity,
    changed_rows,
)

N = 23
TARGET_U = 333
HERE = ANALYSIS_ROOT
DEFAULT_OUTPUT = HERE / "n23_target_search_result.json"
SCHEMA = "grid-graphs.n23-target-construction-search.v1"

# The affine recurrence duplicates rows 9..11 and columns 4..6.  This is their
# radius-two rectangular halo, with inclusive zero-based bounds.
AFFINE_WINDOW = frozenset(
    (row, column) for row in range(7, 14) for column in range(2, 9)
)

# The symbolic recurrence inserts rows 8..10 and appends the packet in columns
# 20..22.  Keep a radius-two row halo and a radius-two-left column halo.  Their
# union is a bounded cross rather than only the seam intersection.
SYMBOLIC_WINDOW = frozenset(
    {(row, column) for row in range(6, 13) for column in range(N)}
    | {(row, column) for row in range(N) for column in range(18, 23)}
)


def rows_sha256(rows: list[str]) -> str:
    return hashlib.sha256(("\n".join(rows) + "\n").encode("ascii")).hexdigest()


def cells(rows: list[str], value: str, window: frozenset[tuple[int, int]]):
    return tuple(sorted(cell for cell in window if rows[cell[0]][cell[1]] == value))


def validate(rows: list[str]) -> tuple[bool, bool]:
    dual = dual_connectivity_check(rows)[0]
    forest = forest_completion_check(rows)[0] if dual else False
    return dual, forest


def exhaustive_two_deletions(rows: list[str]) -> dict:
    """Replay every unordered pair through the canonical connectivity check."""
    source_u = cells(rows, "U", frozenset((r, c) for r in range(N) for c in range(N)))
    generated = connected = forest = 0
    witnesses = []
    for removals in itertools.combinations(source_u, 2):
        generated += 1
        candidate = changed_rows(rows, (), removals)
        dual_ok, forest_ok = validate(candidate)
        connected += dual_ok
        forest += forest_ok
        if forest_ok:
            witnesses.append({"removals": removals, "rows": candidate})
    expected = comb(len(source_u), 2)
    if generated != expected:
        raise AssertionError("two-deletion enumeration was incomplete")
    return {
        "operation": "remove2/add0",
        "eligible_removals": len(source_u),
        "generated": generated,
        "canonical_dual_checks": generated,
        "dual_connected": connected,
        "forest_completable": forest,
        "witnesses": witnesses,
    }


def connected_source_exchange(
    rows: list[str], additions_count: int, removals_count: int
) -> dict:
    """Search one affine seam order with exact individual-removal pruning."""
    sensitivity = ConnectivitySensitivity(rows)
    additions_domain = tuple(cell for cell in sensitivity.source_dots if cell in AFFINE_WINDOW)
    removals_domain = frozenset(cell for cell in sensitivity.source_u if cell in AFFINE_WINDOW)
    histogram: Counter[int] = Counter()
    addition_sets = candidate_tuples = connected = forest = 0
    witnesses = []
    for additions in itertools.combinations(additions_domain, additions_count):
        addition_sets += 1
        removable = tuple(
            cell
            for cell in sensitivity.individually_removable(additions)
            if cell in removals_domain
        )
        histogram[len(removable)] += 1
        augmented = changed_rows(rows, additions, ())
        for removals in itertools.combinations(removable, removals_count):
            candidate_tuples += 1
            candidate = changed_rows(augmented, (), removals)
            dual_ok, forest_ok = validate(candidate)
            connected += dual_ok
            forest += forest_ok
            if forest_ok:
                witnesses.append(
                    {"additions": additions, "removals": removals, "rows": candidate}
                )
    expected_additions = comb(len(additions_domain), additions_count)
    unpruned = expected_additions * comb(len(removals_domain), removals_count)
    if addition_sets != expected_additions:
        raise AssertionError("affine seam addition enumeration was incomplete")
    return {
        "operation": f"remove{removals_count}/add{additions_count}",
        "eligible_additions": len(additions_domain),
        "eligible_removals": len(removals_domain),
        "addition_sets": addition_sets,
        "unpruned_exchange_tuples": unpruned,
        "individual_removal_histogram": dict(sorted(histogram.items())),
        "candidate_removal_tuples_tested": candidate_tuples,
        "monotonic_pruned": unpruned - candidate_tuples,
        "dual_connected": connected,
        "forest_completable": forest,
        "witnesses": witnesses,
    }


def disconnected_source_swaps(rows: list[str], order: int) -> dict:
    """Search equal-count swaps, pruning when additions leave the dual disconnected."""
    additions_domain = cells(rows, ".", SYMBOLIC_WINDOW)
    removals_domain = cells(rows, "U", SYMBOLIC_WINDOW)
    addition_sets = connected_augmentations = candidate_tuples = connected = forest = 0
    witnesses = []
    for additions in itertools.combinations(additions_domain, order):
        addition_sets += 1
        augmented = changed_rows(rows, additions, ())
        if not dual_connectivity_check(augmented)[0]:
            continue
        connected_augmentations += 1
        for removals in itertools.combinations(removals_domain, order):
            candidate_tuples += 1
            candidate = changed_rows(augmented, (), removals)
            dual_ok, forest_ok = validate(candidate)
            connected += dual_ok
            forest += forest_ok
            if forest_ok:
                witnesses.append(
                    {"additions": additions, "removals": removals, "rows": candidate}
                )
    expected_additions = comb(len(additions_domain), order)
    unpruned = expected_additions * comb(len(removals_domain), order)
    if addition_sets != expected_additions:
        raise AssertionError("symbolic swap addition enumeration was incomplete")
    return {
        "operation": f"remove{order}/add{order}",
        "eligible_additions": len(additions_domain),
        "eligible_removals": len(removals_domain),
        "addition_sets": addition_sets,
        "connected_after_additions": connected_augmentations,
        "unpruned_exchange_tuples": unpruned,
        "candidate_removal_tuples_tested": candidate_tuples,
        "connectivity_monotonic_pruned": unpruned - candidate_tuples,
        "dual_connected": connected,
        "forest_completable": forest,
        "witnesses": witnesses,
    }


def source_record(rows: list[str]) -> dict:
    dual = dual_connectivity_check(rows)
    forest = forest_completion_check(rows)
    return {
        "sha256": rows_sha256(rows),
        "u_count": sum(row.count("U") for row in rows),
        "dual_connected": dual[0],
        "dual_reached": dual[1],
        "dual_total": dual[2],
        "forest_completable": forest[0],
        "forest_reason": forest[1],
        "rows": rows,
    }


def run() -> dict:
    affine = residue_two_affine_pattern(N)
    symbolic = target_charge_candidate(7)
    if sum(row.count("U") for row in affine) != 335 or not all(validate(affine)):
        raise AssertionError("affine A23 is not the expected valid 335-U control")
    if sum(row.count("U") for row in symbolic) != TARGET_U:
        raise AssertionError("symbolic candidate is not at the 333-U target")

    affine_searches = [
        exhaustive_two_deletions(affine),
        connected_source_exchange(affine, 1, 3),
        connected_source_exchange(affine, 2, 4),
    ]
    symbolic_searches = [disconnected_source_swaps(symbolic, order) for order in (1, 2)]
    witnesses = [
        witness
        for search in (*affine_searches, *symbolic_searches)
        for witness in search["witnesses"]
    ]
    return {
        "schema": SCHEMA,
        "status": "SAT" if witnesses else "UNSAT_IN_DECLARED_FINITE_NEIGHBORHOODS",
        "exact_in_declared_scope": True,
        "scope": {
            "n": N,
            "target_u": TARGET_U,
            "coordinates": "zero-based; bounds inclusive",
            "affine_global_search": "all unordered pairs of source U cells",
            "affine_seam": {"duplicated_rows": [9, 11], "duplicated_columns": [4, 6]},
            "affine_window": {"rows": [7, 13], "columns": [2, 8], "cells": len(AFFINE_WINDOW)},
            "symbolic_seam": {"inserted_rows": [8, 10], "appended_columns": [20, 22]},
            "symbolic_window": {
                "definition": "rows 6..12 union columns 18..22",
                "cells": len(SYMBOLIC_WINDOW),
            },
            "negative_claim": "Only the listed sources, windows, and exchange orders are excluded.",
        },
        "method": {
            "canonical_checks": "construction_lab.dual_connectivity_check and forest_completion_check",
            "affine_local_prune": (
                "A connected final graph after deleting S implies the augmented graph after deleting "
                "each singleton in S is connected; non-individually-removable U cells are exact prunes."
            ),
            "symbolic_prune": (
                "Deleting U cells only removes dual edges, so a disconnected graph after all additions "
                "cannot become connected after removals."
            ),
        },
        "affine_source": source_record(affine),
        "affine_searches": affine_searches,
        "symbolic_source": source_record(symbolic),
        "symbolic_searches": symbolic_searches,
        "witnesses": witnesses,
        "n26_open_slab_investigation": (
            "not_run_no_n23_witness" if not witnesses else "required"
        ),
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
