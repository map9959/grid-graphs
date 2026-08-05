#!/usr/bin/env python3
"""Census asynchronous two-sided cap landmarks across residue-two widths."""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter, defaultdict
from pathlib import Path

from census_moving_seam_alignment import (
    PHASE_FRONT_WITNESS,
    d4_orientations,
    load_square_pattern,
)
from diagonal_patterns import residue_two_affine_pattern, residue_two_explicit_pattern
from residue_two_frontier_signatures import (
    RankedFrontierState,
    ranked_open_signature_record,
    replay_rows,
)


HERE = Path(__file__).resolve().parent
DEFAULT_OUTPUT = HERE / "residue_two_landmark_census.json"
SCHEMA = "grid-graphs.residue-two-landmark-census.v1"
DEPTHS = range(2, 7)


def rows_sha256(rows: tuple[str, ...]) -> str:
    return hashlib.sha256(("\n".join(rows) + "\n").encode("ascii")).hexdigest()


def pattern_inputs() -> dict[str, tuple[str, ...]]:
    return {
        "exact14": tuple(residue_two_explicit_pattern(14)),
        "affine17": tuple(residue_two_affine_pattern(17)),
        "affine20": tuple(residue_two_affine_pattern(20)),
        "phase20": tuple(load_square_pattern(PHASE_FRONT_WITNESS)),
        "affine23": tuple(residue_two_affine_pattern(23)),
    }


def state_key(state: RankedFrontierState) -> tuple[int, tuple[int, ...]]:
    return state.previous_u_mask, state.partition


def payload_deltas(
    source: RankedFrontierState, normalized: dict
) -> list[dict] | None:
    projected_count = len(set(normalized["projected_partition"]))
    attachment = normalized["attachment_partition"]
    projected_attachment = attachment[:projected_count]
    if len(set(projected_attachment)) != projected_count:
        return None
    payloads = normalized["component_payloads"]
    result = []
    for source_label, target_label in enumerate(projected_attachment):
        source_component = source.components[source_label]
        target_component = payloads[target_label]
        result.append(
            {
                "source_label": source_label,
                "target_attachment_label": target_label,
                "contains_out": source_label == source.partition[0],
                "delta_vertices": target_component["vertices"] - source_component.vertices,
                "delta_edges": target_component["edges"] - source_component.edges,
                "delta_cycle_rank": (
                    target_component["cycle_rank"] - source_component.cycle_rank
                ),
            }
        )
    return result


def side_matches(
    source_rows: tuple[str, ...],
    target_rows: tuple[str, ...],
    side: str,
) -> list[dict]:
    if side not in ("top", "bottom"):
        raise ValueError("side must be top or bottom")
    source_orientations = d4_orientations(source_rows)
    target_orientations = d4_orientations(target_rows)
    matches = []
    for source_orientation in source_orientations:
        source_materialized = source_orientation.rows
        if side == "bottom":
            source_materialized = tuple(reversed(source_materialized))
        source_trace = replay_rows(source_materialized)
        for target_orientation in target_orientations:
            target_materialized = target_orientation.rows
            if side == "bottom":
                target_materialized = tuple(reversed(target_materialized))
            target_trace = replay_rows(target_materialized)
            for source_depth in DEPTHS:
                source_state = source_trace[source_depth]
                for target_depth in DEPTHS:
                    target_state = target_trace[target_depth]
                    for slab_start in range(len(target_rows) - 3):
                        normalized = ranked_open_signature_record(
                            target_state, slab_start, 0
                        )
                        if normalized["forgotten_only_components"]:
                            continue
                        if (
                            normalized["compressed_previous_u_mask"],
                            tuple(normalized["projected_partition"]),
                        ) != state_key(source_state):
                            continue
                        deltas = payload_deltas(source_state, normalized)
                        if deltas is None:
                            continue
                        projected_count = len(set(normalized["projected_partition"]))
                        matches.append(
                            {
                                "side": side,
                                "source_orientation": source_orientation.name,
                                "target_orientation": target_orientation.name,
                                "source_depth": source_depth,
                                "target_depth": target_depth,
                                "slab_start": slab_start,
                                "source_u_cost": source_state.u_cost,
                                "target_u_cost": target_state.u_cost,
                                "delta_u": target_state.u_cost - source_state.u_cost,
                                "source_cycle_excess": source_state.cycle_excess,
                                "target_cycle_excess": target_state.cycle_excess,
                                "delta_cycle_excess": (
                                    target_state.cycle_excess - source_state.cycle_excess
                                ),
                                "hidden_attachment_labels": normalized[
                                    "attachment_partition"
                                ][projected_count:],
                                "component_deltas": deltas,
                            }
                        )
    return matches


def paired_lanes(top: list[dict], bottom: list[dict]) -> tuple[int, list[dict], dict]:
    bottom_by_lane = defaultdict(list)
    for match in bottom:
        key = (
            match["source_orientation"],
            match["target_orientation"],
            match["slab_start"],
        )
        bottom_by_lane[key].append(match)
    count = 0
    samples = []
    lane_counts = Counter()
    for top_match in top:
        key = (
            top_match["source_orientation"],
            top_match["target_orientation"],
            top_match["slab_start"],
        )
        for bottom_match in bottom_by_lane[key]:
            count += 1
            lane_counts[str(key)] += 1
            if len(samples) < 200:
                samples.append(
                    {
                        "source_orientation": key[0],
                        "target_orientation": key[1],
                        "slab_start": key[2],
                        "top_source_depth": top_match["source_depth"],
                        "top_target_depth": top_match["target_depth"],
                        "bottom_source_depth": bottom_match["source_depth"],
                        "bottom_target_depth": bottom_match["target_depth"],
                        "top_delta_u": top_match["delta_u"],
                        "bottom_delta_u": bottom_match["delta_u"],
                        "top_delta_cycle_excess": top_match["delta_cycle_excess"],
                        "bottom_delta_cycle_excess": bottom_match[
                            "delta_cycle_excess"
                        ],
                    }
                )
    return count, samples, dict(sorted(lane_counts.items()))


def census_pair(identifier: str, source: tuple[str, ...], target: tuple[str, ...]) -> dict:
    top = side_matches(source, target, "top")
    bottom = side_matches(source, target, "bottom")
    pair_count, samples, lane_counts = paired_lanes(top, bottom)
    return {
        "id": identifier,
        "source_n": len(source),
        "target_n": len(target),
        "source_rows_sha256": rows_sha256(source),
        "target_rows_sha256": rows_sha256(target),
        "depths": list(DEPTHS),
        "top_match_count": len(top),
        "bottom_match_count": len(bottom),
        "paired_lane_count": pair_count,
        "paired_lane_counts": lane_counts,
        "top_matches": top,
        "bottom_matches": bottom,
        "paired_lane_samples": samples,
        "complete_samples": pair_count <= len(samples),
    }


def build_artifact() -> dict:
    patterns = pattern_inputs()
    pairs = (
        ("exact14-to-affine17", "exact14", "affine17"),
        ("affine17-to-affine20", "affine17", "affine20"),
        ("affine17-to-phase20", "affine17", "phase20"),
        ("phase20-to-affine23", "phase20", "affine23"),
    )
    records = [
        census_pair(identifier, patterns[source], patterns[target])
        for identifier, source, target in pairs
    ]
    claim = {
        "scope": {
            "kind": "asynchronous-two-sided-cap-landmark-census-v1",
            "depths": list(DEPTHS),
            "orientations": "all-distinct-d4-images",
            "slab_width": 3,
            "match": (
                "compressed mask and projected partition equal; no component is "
                "represented only by forgotten slab ports"
            ),
        },
        "pairs": records,
    }
    identity = {"schema": SCHEMA, "claim": claim}
    canonical = json.dumps(
        identity, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    ).encode("utf-8")
    artifact = {
        "schema": SCHEMA,
        "claim": claim,
        "integrity": {
            "algorithm": "sha256",
            "canonicalization": "canonical-json-v1",
            "claim_sha256": hashlib.sha256(canonical).hexdigest(),
        },
    }
    return json.loads(json.dumps(artifact, sort_keys=True))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()
    artifact = build_artifact()
    args.output.write_text(json.dumps(artifact, indent=2, sort_keys=True) + "\n")
    print(
        "wrote",
        args.output,
        [
            (
                pair["id"],
                pair["top_match_count"],
                pair["bottom_match_count"],
                pair["paired_lane_count"],
            )
            for pair in artifact["claim"]["pairs"]
        ],
    )


if __name__ == "__main__":
    main()
