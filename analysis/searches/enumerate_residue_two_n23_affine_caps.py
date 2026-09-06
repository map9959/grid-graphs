#!/usr/bin/env python3
"""Exact, lightweight census of n=23 affine prefix and suffix caps.

This enumerates caps and their single-row phase-front domains only.  It does
not search the rows between a top and bottom cap, and a charge-feasible pair
is not asserted to be topologically compatible.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path

from analysis._paths import analysis_path
from analysis.patterns.construction_lab import q_old_formula
from analysis.patterns.diagonal_patterns import q_formula, residue_two_affine_pattern
from analysis.searches.search_residue_two_phase_front import PHASE_ALPHABET, row_words
from analysis.tiles.tile_grammar import (
    ROW_PACKET_ALPHABET,
    FrontierState,
    advance_row,
    initial_state,
    render_mask,
    row_mask,
)

N = 23
PACKET_COUNT = 7
ROW_BASELINE = 2 * PACKET_COUNT
DEPTHS = tuple(range(2, 7))
TARGETS = (q_old_formula(N), q_formula(N))
SCHEMA = "grid-graphs.residue-two-n23-affine-cap-census.v1"
DEFAULT_RESULT = analysis_path("residue_two_n23_affine_caps_result.json")


def d4_transforms(rows: list[str]) -> tuple[tuple[str, list[str]], ...]:
    """Return all eight named D4 actions, rejecting an accidental collision."""

    rotations = []
    current = list(rows)
    for _ in range(4):
        rotations.append(current)
        current = ["".join(row[column] for row in reversed(current)) for column in range(N)]
    transformed = tuple(
        [(f"rotate_{90 * index}", value) for index, value in enumerate(rotations)]
        + [(f"rotate_{90 * index}_reflect_lr", [row[::-1] for row in value])
           for index, value in enumerate(rotations)]
    )
    if len({tuple(value) for _, value in transformed}) != 8:
        raise AssertionError("the n=23 affine pattern does not have eight distinct D4 transforms")
    return transformed


def construct_state(rows: list[str]) -> FrontierState:
    state = initial_state(N)
    for row in rows:
        child = advance_row(state, row_mask(row))
        if child is None:
            raise AssertionError("an affine cap sealed a dual component")
        state = child
    return state


def phase_row(word: str, mode: str) -> str:
    alphabet = ROW_PACKET_ALPHABET if mode == "basic" else PHASE_ALPHABET
    return "." + "".join(alphabet[name] for name in word) + "."


def frontier_diagnostics(state: FrontierState) -> dict:
    out = state.partition[0]
    sizes = Counter(state.partition[1:])
    labels = set(state.partition)
    return {
        "components_including_out": len(set(state.partition)),
        "out_frontier_faces": sizes[out],
        "non_out_frontier_faces": len(state.partition) - 1 - sizes[out],
        "non_out_components": sum(label != out for label in sizes),
        "frontier_component_sizes_including_zero_out": sorted(
            (sizes.get(label, 0) for label in labels), reverse=True
        ),
        "cycle_excess": state.cycle_excess,
    }


def state_json(state: FrontierState) -> dict:
    return {
        "row_index": state.row_index,
        "previous_row": render_mask(state.previous_u_mask, N),
        "partition": list(state.partition),
        "u_cost": state.u_cost,
        "cycle_excess": state.cycle_excess,
    }


def next_row_stats(state: FrontierState, mode: str) -> dict:
    words = row_words(PACKET_COUNT, mode)
    live: list[tuple[str, FrontierState]] = []
    for word in words:
        row = phase_row(word, mode)
        child = advance_row(state, row_mask(row))
        if child is not None:
            live.append((row, child))
    outgoing = {child for _, child in live}
    return {
        "domain_rows": len(words),
        "live_next_rows": len(live),
        "outgoing_full_states": len(outgoing),
        "sealed_rows": len(words) - len(live),
        "representative_live_row": live[0][0] if live else None,
    }


def attainable_gap_charges(rows: int, mode: str) -> set[int]:
    """Return exact total normalized charges for the unconstrained row language."""

    alphabet = ROW_PACKET_ALPHABET if mode == "basic" else PHASE_ALPHABET
    row_charges = {
        sum(alphabet[name].count("U") - 2 for name in word)
        for word in row_words(PACKET_COUNT, mode)
    }
    totals = {0}
    for _ in range(rows):
        totals = {left + right for left in totals for right in row_charges}
    return totals


def _source_hash(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def census() -> dict:
    affine = residue_two_affine_pattern(N)
    transformed = d4_transforms(affine)
    sections: dict[str, dict[str, list[dict]]] = {"top": {}, "bottom": {}}

    for side in sections:
        for depth in DEPTHS:
            groups: dict[FrontierState, list[dict]] = {}
            for transform_name, rows in transformed:
                physical = rows[:depth] if side == "top" else rows[-depth:]
                processed = physical if side == "top" else list(reversed(physical))
                state = construct_state(processed)
                groups.setdefault(state, []).append(
                    {"transform": transform_name, "physical_rows": physical}
                )

            records = []
            for ordinal, (state, sources) in enumerate(groups.items()):
                records.append(
                    {
                        "id": f"{side[0]}{depth}-{ordinal}",
                        "cap_u_cost": state.u_cost,
                        "normalized_charge": state.u_cost - ROW_BASELINE * depth,
                        "provenance": sources,
                        "processing_order": "physical" if side == "top" else "reversed_physical_rows",
                        "full_state": state_json(state),
                        "frontier_diagnostics": frontier_diagnostics(state),
                        "next_rows": {
                            mode: next_row_stats(state, mode) for mode in ("basic", "phase")
                        },
                    }
                )
            sections[side][str(depth)] = {
                "cap_instances": len(transformed),
                "deduplicated_full_states": len(records),
                "states": records,
            }

    pairings = []
    for target in TARGETS:
        target_charge = target - ROW_BASELINE * N
        for top_depth in DEPTHS:
            for bottom_depth in DEPTHS:
                tops = sections["top"][str(top_depth)]["states"]
                bottoms = sections["bottom"][str(bottom_depth)]["states"]
                gap_rows = N - top_depth - bottom_depth
                mode_results = {}
                for mode in ("basic", "phase"):
                    attainable = attainable_gap_charges(gap_rows, mode)
                    pairs = [
                        (top, bottom)
                        for top in tops
                        for bottom in bottoms
                        if target_charge
                        - top["normalized_charge"]
                        - bottom["normalized_charge"] in attainable
                    ]
                    live_pairs = [
                        (top, bottom)
                        for top, bottom in pairs
                        if top["next_rows"][mode]["live_next_rows"] > 0
                        and bottom["next_rows"][mode]["live_next_rows"] > 0
                    ]
                    representative = live_pairs[0] if live_pairs else None
                    mode_results[mode] = {
                        "charge_arithmetic_feasible_full_state_pairs": len(pairs),
                        "charge_arithmetic_feasible_provenance_pairs": sum(
                            len(top["provenance"]) * len(bottom["provenance"])
                            for top, bottom in pairs
                        ),
                        "one_step_live_full_state_pairs": len(live_pairs),
                        "one_step_live_provenance_pairs": sum(
                            len(top["provenance"]) * len(bottom["provenance"])
                            for top, bottom in live_pairs
                        ),
                        "same_transform_provenance_pairs": sum(
                            sum(
                                left["transform"] == right["transform"]
                                for left in top["provenance"]
                                for right in bottom["provenance"]
                            )
                            for top, bottom in live_pairs
                        ),
                        "representative_pair": (
                            [representative[0]["id"], representative[1]["id"]]
                            if representative else None
                        ),
                        "representative_required_gap_charge": (
                            target_charge
                            - representative[0]["normalized_charge"]
                            - representative[1]["normalized_charge"]
                            if representative else None
                        ),
                    }
                pairings.append(
                    {
                        "target_u": target,
                        "target_kind": (
                            "exact_332" if target == TARGETS[0] else "surplus_333"
                        ),
                        "top_depth": top_depth,
                        "bottom_depth": bottom_depth,
                        "unsearched_gap_rows": gap_rows,
                        "target_total_normalized_charge": target_charge,
                        "modes": mode_results,
                        "merge_profile": None,
                    }
                )

    source = Path(__file__)
    dependencies = [
        source,
        analysis_path("diagonal_patterns.py"),
        analysis_path("construction_lab.py"),
        analysis_path("search_residue_two_middle.py"),
        analysis_path("search_residue_two_phase_front.py"),
        analysis_path("tile_grammar.py"),
    ]
    return {
        "schema": SCHEMA,
        "exact": True,
        "scope": {
            "n": N,
            "affine_u_cost": sum(row.count("U") for row in affine),
            "distinct_d4_transforms": len(transformed),
            "depths": list(DEPTHS),
            "next_row_language": "complete L*/(X|H)+/R* or L*/(X|H|S)+/R*, center width 1..5",
            "packet_count": PACKET_COUNT,
            "row_baseline_u": ROW_BASELINE,
            "normalized_cap_charge": "cap_u_cost - row_baseline_u * depth",
            "deduplication_key": "full FrontierState",
            "partition_projection": None,
            "middle_search": None,
            "cap_pairing": (
                "all ordered top-depth/bottom-depth pairs; top and bottom D4 "
                "transforms may be selected independently"
            ),
        },
        "provenance": {
            "affine_generator": "diagonal_patterns.residue_two_affine_pattern(23)",
            "affine_rows_sha256": hashlib.sha256("\n".join(affine).encode()).hexdigest(),
            "transforms": [name for name, _ in transformed],
            "source_files": {
                path.name: _source_hash(path) for path in dependencies
            },
        },
        "caps": sections,
        "pairings": pairings,
        "pairing_interpretation": (
            "Pairs are filtered by exact charge attainability and separately by whether "
            "both caps admit a declared next row. All leave an unsearched gap, so no "
            "merge profile or direct compatibility is claimed."
        ),
    }


def write_cap_seed(record: dict, path: Path, target: int, mode: str = "phase") -> None:
    candidates = [
        item for item in record["pairings"]
        if item["target_u"] == target
        and item["modes"][mode]["representative_pair"] is not None
    ]
    if not candidates:
        raise ValueError(f"no charge-feasible cap pair for target {target}")
    pairing = max(
        candidates, key=lambda item: item["top_depth"] + item["bottom_depth"]
    )
    top_depth = pairing["top_depth"]
    bottom_depth = pairing["bottom_depth"]
    mode_pairing = pairing["modes"][mode]
    top_id, bottom_id = mode_pairing["representative_pair"]
    top = next(
        item for item in record["caps"]["top"][str(top_depth)]["states"]
        if item["id"] == top_id
    )
    bottom = next(
        item for item in record["caps"]["bottom"][str(bottom_depth)]["states"]
        if item["id"] == bottom_id
    )
    seed = {
        "schema": "grid-graphs.cap-seed.v1",
        "label": "cap seed, not witness",
        "target_u": target,
        "middle_row_mode": mode,
        "top_cap_rows": top["provenance"][0]["physical_rows"],
        "bottom_cap_rows": bottom["provenance"][0]["physical_rows"],
        "unsearched_gap_rows": N - top_depth - bottom_depth,
        "required_gap_normalized_charge": mode_pairing["representative_required_gap_charge"],
        "warning": "Charge-feasible caps only; middle rows and direct compatibility were not searched.",
    }
    path.write_text(json.dumps(seed, indent=2) + "\n")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_RESULT)
    parser.add_argument("--cap-seed", type=Path)
    parser.add_argument("--seed-target", type=int, choices=TARGETS, default=TARGETS[0])
    args = parser.parse_args()
    record = census()
    args.output.write_text(json.dumps(record, separators=(",", ":")) + "\n")
    if args.cap_seed is not None:
        write_cap_seed(record, args.cap_seed, args.seed_target)
    print(
        f"wrote exact n={N} census: "
        f"{sum(depth['deduplicated_full_states'] for side in record['caps'].values() for depth in side.values())} "
        f"deduplicated cap states -> {args.output}"
    )


if __name__ == "__main__":
    main()
