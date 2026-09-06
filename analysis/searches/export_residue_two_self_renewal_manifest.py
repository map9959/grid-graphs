#!/usr/bin/env python3
"""Export the exact B20-to-B23 cap-to-cap self-renewal transfer language."""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from collections import defaultdict
from pathlib import Path

from analysis.transport.census_moving_seam_alignment import PHASE_FRONT_WITNESS, load_square_pattern
from analysis.residue_certificates.residue_two_frontier_signatures import (
    initial_ranked_state,
    ordinary_state,
    ranked_advance_row,
    ranked_open_signature_record,
    replay_rows,
)
from analysis.searches.search_residue_two_b_state_phase_pump import phase_masks_for_edge
from analysis.searches.search_residue_two_moving_seam import (
    AlignmentState,
    AlignmentTransition,
    build_alignment_automaton,
    enumerate_domain_rows,
)
from analysis.tiles.tile_grammar import row_mask
from analysis._paths import ANALYSIS_ROOT


HERE = ANALYSIS_ROOT
DEFAULT_OUTPUT = HERE / "residue_two_b20_self_renewal_manifest.json"
SCHEMA = "grid-graphs.residue-two-frontier-manifest.v1"
TARGET_N = 23
CUT = 11
TOP_CAP_ROWS = 3
BOTTOM_CAP_ROWS = 2


def rows_sha256(rows: tuple[str, ...]) -> str:
    return hashlib.sha256(("\n".join(rows) + "\n").encode("ascii")).hexdigest()


def state_record(state, masks: tuple[int, ...]) -> dict:
    return {
        "previous_u": state.previous_u_mask,
        "partition": list(state.partition),
        "cost": state.u_cost,
        "cycles": state.cycle_excess,
        "cap_masks": list(masks),
    }


def cap_domain(source_row: str, seam: int) -> tuple[int, ...]:
    return tuple(
        sorted(row_mask(row) for row in enumerate_domain_rows(source_row, seam, 0))
    )


def cap_seeds(source: tuple[str, ...], seam: int, side: str) -> list[dict]:
    if side == "top":
        source_rows = source[:TOP_CAP_ROWS]
        source_state = replay_rows(source)[TOP_CAP_ROWS]
    elif side == "bottom":
        source_rows = tuple(reversed(source[-BOTTOM_CAP_ROWS:]))
        source_state = replay_rows(tuple(reversed(source)))[BOTTOM_CAP_ROWS]
    else:
        raise ValueError("side must be top or bottom")
    domains = [cap_domain(row, seam) for row in source_rows]
    seeds = {}
    for masks in itertools.product(*domains):
        target_state = initial_ranked_state(TARGET_N)
        for mask in masks:
            outgoing = ranked_advance_row(target_state, mask)
            if outgoing is None:
                break
            target_state = outgoing
        else:
            normalized = ranked_open_signature_record(
                target_state, 1 + 3 * seam, 0
            )
            if normalized["forgotten_only_components"]:
                continue
            if (
                normalized["compressed_previous_u_mask"],
                tuple(normalized["projected_partition"]),
            ) != (source_state.previous_u_mask, source_state.partition):
                continue
            key = ordinary_state(target_state)
            seeds.setdefault(key, state_record(target_state, masks))
    return list(seeds.values())


def fixed_bottom_alignment_states(
    automaton, seam: int
) -> set[AlignmentState]:
    row22 = [
        edge
        for edge in automaton.forward[22]
        if edge.operation == "ADVANCE" and edge.source_row == 19 and edge.seam == seam
    ]
    final_before = {edge.before for edge in row22 if edge.after in automaton.layers[23]}
    row21 = [
        edge
        for edge in automaton.forward[21]
        if edge.operation == "ADVANCE"
        and edge.source_row == 18
        and edge.seam == seam
        and edge.after in final_before
    ]
    return {edge.before for edge in row21}


def fixed_top_alignment_state(automaton, seam: int) -> AlignmentState | None:
    current = automaton.layers[0][0]
    for row in range(TOP_CAP_ROWS):
        edge = next(
            (
                edge
                for edge in automaton.forward[row]
                if edge.before == current
                and edge.operation == "ADVANCE"
                and edge.source_row == row
                and edge.seam == seam
            ),
            None,
        )
        if edge is None:
            return None
        current = edge.after
    return current


def trim_middle_lane(
    automaton,
    source: tuple[str, ...],
    seam: int,
) -> tuple[dict[int, set[AlignmentState]], dict[int, list[tuple[AlignmentTransition, tuple[int, ...]]]]]:
    top = fixed_top_alignment_state(automaton, seam)
    bottoms = fixed_bottom_alignment_states(automaton, seam)
    if top is None or not bottoms:
        return {}, {}
    eligible = {}
    for row in range(TOP_CAP_ROWS, TARGET_N - BOTTOM_CAP_ROWS):
        edges = []
        for edge in automaton.forward[row]:
            masks = phase_masks_for_edge(
                source[edge.source_row], row, edge.seam, 3, "phase"
            )
            if masks:
                edges.append((edge, masks))
        eligible[row] = edges

    reachable = {TOP_CAP_ROWS: {top}}
    for row in range(TOP_CAP_ROWS, TARGET_N - BOTTOM_CAP_ROWS):
        reachable[row + 1] = {
            edge.after
            for edge, _ in eligible[row]
            if edge.before in reachable[row]
        }
    completable = {TARGET_N - BOTTOM_CAP_ROWS: bottoms & reachable[TARGET_N - BOTTOM_CAP_ROWS]}
    retained = {}
    for row in range(TARGET_N - BOTTOM_CAP_ROWS - 1, TOP_CAP_ROWS - 1, -1):
        retained[row] = [
            (edge, masks)
            for edge, masks in eligible[row]
            if edge.before in reachable[row] and edge.after in completable[row + 1]
        ]
        completable[row] = {edge.before for edge, _ in retained[row]}
    if top not in completable[TOP_CAP_ROWS]:
        return {}, {}
    layers = {
        row: reachable[row] & completable[row]
        for row in range(TOP_CAP_ROWS, TARGET_N - BOTTOM_CAP_ROWS + 1)
    }
    return layers, retained


def build_manifest() -> dict:
    source = tuple(load_square_pattern(PHASE_FRONT_WITNESS))
    automaton = build_alignment_automaton(20, TARGET_N, 7)
    domains: list[tuple[int, ...]] = []
    domain_ids = {}

    def domain_id(masks: tuple[int, ...]) -> int:
        if masks not in domain_ids:
            domain_ids[masks] = len(domains)
            domains.append(masks)
        return domain_ids[masks]

    signature_ids = {}
    signature_states = []

    def signature_id(lane: int, layer: int, state: AlignmentState) -> int:
        key = (lane, layer, state)
        if key not in signature_ids:
            signature_ids[key] = len(signature_states)
            signature_states.append(
                {
                    "id": signature_ids[key],
                    "layer": layer,
                    "lane": lane,
                    "alignment": {
                        "cursor": state.cursor,
                        "holds": state.holds,
                        "previous_seam": state.previous_seam,
                        "baseline_hold_removals": state.baseline_hold_removals,
                        "baseline_advance_insertions": state.baseline_advance_insertions,
                    },
                }
            )
        return signature_ids[key]

    transitions = []
    top_seeds = []
    bottom_seeds = []
    lane_records = []
    for seam in range(7):
        layers, retained = trim_middle_lane(automaton, source, seam)
        top = cap_seeds(source, seam, "top")
        bottom = cap_seeds(source, seam, "bottom")
        if not layers or not top or not bottom:
            lane_records.append(
                {
                    "lane": seam,
                    "slab_start": 1 + 3 * seam,
                    "top_seeds": len(top),
                    "bottom_seeds": len(bottom),
                    "active": False,
                }
            )
            continue
        for row, states in layers.items():
            for state in sorted(states):
                signature_id(seam, row, state)
        top_alignment = fixed_top_alignment_state(automaton, seam)
        assert top_alignment is not None
        top_signature = signature_id(seam, TOP_CAP_ROWS, top_alignment)
        bottom_alignments = fixed_bottom_alignment_states(automaton, seam)
        active_bottom = bottom_alignments & layers[TARGET_N - BOTTOM_CAP_ROWS]
        for seed in top:
            top_seeds.append({"signature": top_signature, "state": seed})
        for alignment in sorted(active_bottom):
            bottom_signature = signature_id(
                seam, TARGET_N - BOTTOM_CAP_ROWS, alignment
            )
            for seed in bottom:
                bottom_seeds.append({"signature": bottom_signature, "state": seed})
        for row in range(TOP_CAP_ROWS, TARGET_N - BOTTOM_CAP_ROWS):
            for edge, masks in retained[row]:
                transitions.append(
                    {
                        "id": len(transitions),
                        "row": row,
                        "before": signature_id(seam, row, edge.before),
                        "after": signature_id(seam, row + 1, edge.after),
                        "domain_id": domain_id(masks),
                        "operation": edge.operation,
                        "source_row": edge.source_row,
                        "seam": edge.seam,
                        "lane": seam,
                    }
                )
        lane_records.append(
            {
                "lane": seam,
                "slab_start": 1 + 3 * seam,
                "top_seeds": len(top),
                "bottom_seeds": len(bottom) * len(active_bottom),
                "middle_states": sum(len(states) for states in layers.values()),
                "middle_transitions": sum(len(edges) for edges in retained.values()),
                "active": True,
            }
        )

    manifest = {
        "schema": SCHEMA,
        "target_n": TARGET_N,
        "cut": CUT,
        "u_limit": 335,
        "join_budgets": [335, 333],
        "top_start_row": TOP_CAP_ROWS,
        "bottom_start_row": TARGET_N - BOTTOM_CAP_ROWS,
        "source": {
            "n": len(source),
            "u_count": sum(row.count("U") for row in source),
            "rows_sha256": rows_sha256(source),
        },
        "mask_domains": [
            {"id": index, "masks": list(masks)}
            for index, masks in enumerate(domains)
        ],
        "signature_states": sorted(signature_states, key=lambda item: item["id"]),
        "signature_transitions": transitions,
        "top_seeds": top_seeds,
        "bottom_seeds": bottom_seeds,
        "lanes": lane_records,
        "provenance": {
            "carrier_mode": "phase-XHS-center-width-at-most-five",
            "schedule_mode": "all-middle-schedules-fixed-self-renewing-caps",
            "cap_mode": "exact-radius-zero-inserted-packet-lift",
            "radius": 3,
            "strict_boundaries": True,
            "top_cap_rows": TOP_CAP_ROWS,
            "bottom_cap_rows": BOTTOM_CAP_ROWS,
        },
    }
    return json.loads(json.dumps(manifest, sort_keys=True))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()
    manifest = build_manifest()
    args.output.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    print(
        f"wrote {args.output}: domains={len(manifest['mask_domains'])} "
        f"states={len(manifest['signature_states'])} "
        f"transitions={len(manifest['signature_transitions'])} "
        f"top_seeds={len(manifest['top_seeds'])} "
        f"bottom_seeds={len(manifest['bottom_seeds'])}"
    )
    print(manifest["lanes"])


if __name__ == "__main__":
    main()
