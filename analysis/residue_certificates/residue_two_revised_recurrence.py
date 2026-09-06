#!/usr/bin/env python3
"""Symbolic probes for the revised residue-two recurrence.

The target-charge candidate deliberately implements the simplest recurrence
licensed by the packet accounting: append one zero-charge R packet to every
old mutable row and insert three charge-one rows.  It is useful as a precise
negative control; it is not returned as a construction when disconnected.
"""

from __future__ import annotations

import argparse

from analysis._paths import ANALYSIS_ROOT
from analysis.patterns.construction_lab import (
    dual_connectivity_check,
    forest_completion_check,
)
from analysis.patterns.diagonal_patterns import residue_two_affine_pattern

HERE = ANALYSIS_ROOT
B20 = HERE / "residue_two_phase_front_witness.txt"


def revised_target(k: int) -> int:
    if k < 5:
        raise ValueError("the revised target starts at k=5")
    return 6 * k * k + 5 * k + 4


def load_b20() -> list[str]:
    rows = [line.strip() for line in B20.read_text().splitlines() if line.strip()]
    if len(rows) != 20 or any(len(row) != 20 for row in rows):
        raise ValueError(f"invalid B20 control at {B20}")
    return rows


def _hold_row(packet_count: int) -> str:
    """A charge-one row: H R^(packet_count-1), with dot boundaries."""
    return "." + "UUU" + ".UU" * (packet_count - 1) + "."


def target_charge_step(rows: list[str]) -> list[str]:
    """Apply the uniform-right exact-charge packet recurrence once.

    Five cap rows are replaced by the corresponding affine caps.  Mutable rows
    gain an R packet, and three H-bearing rows are inserted after five mutable
    rows.  This realizes the required count increment but need not preserve the
    rooted dual attachment state.
    """
    n = len(rows)
    if n < 20 or n % 3 != 2 or any(len(row) != n for row in rows):
        raise ValueError("target_charge_step requires a square n=3k+2 pattern, n>=20")
    k = (n - 2) // 3
    mutable = rows[3:-2]
    if len(mutable) != 3 * k - 3 or any(row[0] != "." or row[-1] != "." for row in mutable):
        raise ValueError("source does not have the five-cap packet form")

    widened = [row[:-1] + ".UU." for row in mutable]
    widened[5:5] = [_hold_row(k + 1)] * 3
    cap = residue_two_affine_pattern(n + 3)
    result = [*cap[:3], *widened, *cap[-2:]]
    expected_increment = 12 * k + 11
    if sum(row.count("U") for row in result) - sum(row.count("U") for row in rows) != expected_increment:
        raise AssertionError("target-charge recurrence count changed")
    return result


def target_charge_candidate(k: int) -> list[str]:
    """Generate the uniform-right target-charge probe for k>=6."""
    if k < 6:
        raise ValueError("the symbolic target-charge probe is based at B20 (k=6)")
    rows = load_b20()
    for _ in range(6, k):
        rows = target_charge_step(rows)
    if sum(row.count("U") for row in rows) != revised_target(k):
        raise AssertionError("target-charge candidate has the wrong total")
    return rows


def affine_step(rows: list[str]) -> list[str]:
    """The established affine row/column duplication recurrence."""
    n = len(rows)
    if n < 17 or n % 3 != 2 or any(len(row) != n for row in rows):
        raise ValueError("affine_step requires a square n=3k+2 pattern, n>=17")
    row_indices = [*range(9), 9, 10, 11, *range(9, n)]
    column_indices = [*range(4), 4, 5, 6, *range(4, n)]
    return ["".join(rows[row][column] for column in column_indices) for row in row_indices]


def affine_candidate(k: int) -> list[str]:
    """Generate the strongest known connected recurrence from the A17 base."""
    if k < 5:
        raise ValueError("affine_candidate requires k>=5")
    rows = residue_two_affine_pattern(17)
    for _ in range(5, k):
        rows = affine_step(rows)
    return rows


def metrics(rows: list[str]) -> dict[str, int | bool | str]:
    connected, reached, total = dual_connectivity_check(rows)
    forest, reason = forest_completion_check(rows)
    return {
        "n": len(rows),
        "u": sum(row.count("U") for row in rows),
        "dual_connected": connected,
        "dual_reached": reached,
        "dual_total": total,
        "forest_completable": forest,
        "forest_reason": reason,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--maximum-k", type=int, default=40)
    args = parser.parse_args()
    if args.maximum_k < 6:
        parser.error("--maximum-k must be at least 6")

    for family, start, generator in (
        ("target-charge-probe", 6, target_charge_candidate),
        ("affine-connected", 5, affine_candidate),
    ):
        for k in range(start, args.maximum_k + 1):
            print(family, k, metrics(generator(k)))


if __name__ == "__main__":
    main()
