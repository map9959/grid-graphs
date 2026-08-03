#!/usr/bin/env python3
"""Run and aggregate exact affine one-HOLD moving-seam schedule shards.

Each shard is one deterministic complete operation word. It builds frontiers
once at U limit 179 with radius-one packets, fixed affine cap rows, and one
global boundary-cell rewrite, then performs cached cost-bucket joins at 179 and
178. Completed artifacts and ``aggregate.json`` are written atomically.

Examples::

    python analysis/run_residue_two_moving_seam_shards.py --workers 8 \
        --output-dir data/moving-seam-shards --resume
    python analysis/run_residue_two_moving_seam_shards.py --workers 2 \
        --output-dir /tmp/seams --shards 0-2,7

``--shards`` accepts comma-separated zero-based indices and inclusive ranges.
No expensive search runs merely by importing this module.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from dataclasses import asdict
from pathlib import Path
from typing import Sequence

from search_residue_two_moving_seam import (
    DEFAULT_FIXED_ROWS,
    affine_one_hold_relocation_schedule,
    build_bidirectional_frontiers,
    compatible_schedule_operation_word_shards,
    join_bidirectional_frontiers,
    operation_word_hash,
    write_result,
)

SHARD_SCHEMA = "grid-graphs.residue-two-moving-seam-shard.v1"
AGGREGATE_SCHEMA = "grid-graphs.residue-two-moving-seam-shard-aggregate.v1"
EXPECTED_SHARD_COUNT = 21


def _words_hash(words: Sequence[Sequence[str]]) -> str:
    payload = json.dumps(
        [list(word) for word in words], separators=(",", ":"), sort_keys=False
    ).encode()
    return hashlib.sha256(payload).hexdigest()


def production_shards():
    """Build the deterministic production shard manifest and schedules."""
    parent = affine_one_hold_relocation_schedule()
    shards = compatible_schedule_operation_word_shards(parent)
    if len(shards) != EXPECTED_SHARD_COUNT:
        raise AssertionError(f"expected 21 operation words, found {len(shards)}")
    if sum(shard.complete_path_count for shard in shards) != parent.complete_path_count:
        raise AssertionError("shard seam-path counts do not sum to the parent count")
    return parent, shards


def _join_record(result, join_seconds: float) -> dict[str, object]:
    return {
        "u_count": result.u_count,
        "conclusion": result.conclusion,
        "complete": result.complete,
        "top_states": result.top_states,
        "bottom_states": result.bottom_states,
        "join_stats": asdict(result.join_stats),
        "witness": list(result.witness) if result.witness is not None else None,
        "steps": [asdict(step) for step in result.steps] if result.steps else None,
        "validation": result.validation,
        "join_seconds": join_seconds,
    }


def run_shard(index: int, output_dir: Path, cut: int = 8) -> Path:
    """Run one production shard and atomically publish it after both joins."""
    started = time.monotonic()
    parent, shards = production_shards()
    shard = shards[index]
    if not shard.metadata.get("fixed_target_has_representation"):
        raise AssertionError("shard lacks fixed affine target membership")
    words = tuple(tuple(item.metadata["operation_word"]) for item in shards)

    frontiers = build_bidirectional_frontiers(
        u_limit=179,
        cut=cut,
        fixed_rows=DEFAULT_FIXED_ROWS,
        schedule=shard,
        boundary_rewrites=1,
    )
    join_started = time.monotonic()
    result_179 = join_bidirectional_frontiers(
        frontiers, u_count=179, boundary_rewrites=1, bucketed=True, use_cache=True
    )
    join_179_seconds = time.monotonic() - join_started
    join_started = time.monotonic()
    result_178 = join_bidirectional_frontiers(
        frontiers, u_count=178, boundary_rewrites=1, bucketed=True, use_cache=True
    )
    join_178_seconds = time.monotonic() - join_started

    word = tuple(shard.metadata["operation_word"])
    record = {
        "schema": SHARD_SCHEMA,
        "completion": True,
        "operation_word_index": index,
        "operation_word": list(word),
        "operation_word_hash": operation_word_hash(word),
        "all_operation_words_hash": _words_hash(words),
        "seam_path_count": shard.complete_path_count,
        "layer_state_counts": list(shard.layer_state_counts),
        "layer_edge_counts": list(shard.layer_edge_counts),
        "fixed_affine_target_membership": True,
        "scope": {
            "parent_schedule": parent.name,
            "source_n": 14,
            "target_n": 17,
            "radius": 1,
            "tube_packets": "arbitrary radius-one packet domains",
            "fixed_rows": list(DEFAULT_FIXED_ROWS),
            "fixed_caps": "residue_two_affine_pattern(17)",
            "boundary_rewrite_budget": 1,
            "u_frontier_limit": 179,
            "join_u_counts": [179, 178],
            "cut": cut,
        },
        "frontiers": {
            "top_states": len(frontiers.top),
            "bottom_states": len(frontiers.bottom),
            "top_stats": [asdict(item) for item in frontiers.top_stats],
            "bottom_stats": [asdict(item) for item in frontiers.bottom_stats],
            "build_seconds": frontiers.elapsed_seconds,
        },
        "joins": {
            "179": _join_record(result_179, join_179_seconds),
            "178": _join_record(result_178, join_178_seconds),
        },
        "positive_control_179": (
            "VALIDATED_SAT"
            if result_179.conclusion == "SAT"
            and result_179.validation
            and result_179.validation.get("accepted")
            else "NOT_VALIDATED_SAT"
        ),
        "timings": {"total_seconds": time.monotonic() - started},
    }
    output = output_dir / f"shard-{index:02d}.json"
    write_result(output, record)
    return output


def validate_shard_artifact(
    record: dict, index: int, expected_shards=None
) -> dict:
    """Validate identity, completeness, scope, and witness claims of an artifact."""
    if expected_shards is None:
        _, expected_shards = production_shards()
    expected = expected_shards[index]
    words = tuple(tuple(item.metadata["operation_word"]) for item in expected_shards)
    word = tuple(expected.metadata["operation_word"])
    failures = []
    if record.get("schema") != SHARD_SCHEMA or record.get("completion") is not True:
        failures.append("schema/completion")
    if record.get("operation_word_index") != index:
        failures.append("operation word index")
    if tuple(record.get("operation_word", ())) != word:
        failures.append("operation word")
    if record.get("operation_word_hash") != operation_word_hash(word):
        failures.append("operation word hash")
    if record.get("all_operation_words_hash") != _words_hash(words):
        failures.append("operation-word manifest hash")
    if record.get("seam_path_count") != expected.complete_path_count:
        failures.append("seam path count")
    if record.get("layer_state_counts") != list(expected.layer_state_counts):
        failures.append("layer state counts")
    if record.get("layer_edge_counts") != list(expected.layer_edge_counts):
        failures.append("layer edge counts")
    if record.get("fixed_affine_target_membership") is not True:
        failures.append("fixed affine target membership")
    frontiers = record.get("frontiers", {})
    if not all(
        isinstance(frontiers.get(key), int) and frontiers[key] >= 0
        for key in ("top_states", "bottom_states")
    ) or not all(
        isinstance(frontiers.get(key), list)
        for key in ("top_stats", "bottom_stats")
    ):
        failures.append("frontier statistics")
    scope = record.get("scope", {})
    expected_scope = {
        "parent_schedule": "affine-one-hold-relocation",
        "source_n": 14,
        "target_n": 17,
        "radius": 1,
        "fixed_rows": list(DEFAULT_FIXED_ROWS),
        "boundary_rewrite_budget": 1,
        "u_frontier_limit": 179,
        "join_u_counts": [179, 178],
    }
    if any(scope.get(key) != value for key, value in expected_scope.items()):
        failures.append("scope")
    joins = record.get("joins", {})
    for budget in (179, 178):
        join = joins.get(str(budget), {})
        if join.get("u_count") != budget or join.get("complete") is not True:
            failures.append(f"join {budget} completeness")
            continue
        if join.get("conclusion") not in ("SAT", "UNSAT_IN_LANGUAGE"):
            failures.append(f"join {budget} conclusion")
        if join.get("conclusion") == "SAT" and not (
            join.get("witness")
            and join.get("validation", {}).get("accepted") is True
        ):
            failures.append(f"join {budget} witness validation")
        if budget == 179 and join.get("conclusion") == "SAT" and (
            join.get("validation", {}).get("u_count") != 179
        ):
            failures.append("join 179 exact control count")
        stats = join.get("join_stats", {})
        if not all(
            isinstance(stats.get(key), int) and stats[key] >= 0
            for key in (
                "alignment_buckets",
                "candidate_state_pairs",
                "cost_pruned_pairs",
                "merged_pairs",
                "connected_pairs",
                "cache_hits",
                "merge_evaluations",
                "scope_pruned_pairs",
            )
        ):
            failures.append(f"join {budget} statistics")
    join_179 = joins.get("179", {})
    expected_control = (
        "VALIDATED_SAT"
        if join_179.get("conclusion") == "SAT"
        and join_179.get("witness")
        and join_179.get("validation", {}).get("accepted") is True
        else "NOT_VALIDATED_SAT"
    )
    if record.get("positive_control_179") != expected_control:
        failures.append("positive control 179")
    if failures:
        raise ValueError(f"invalid shard {index}: {', '.join(failures)}")
    return record


def aggregate_artifacts(
    output_dir: Path,
    requested_indices: Sequence[int],
    *,
    write: bool = True,
) -> dict:
    """Validate and aggregate requested artifacts without deduplicating patterns."""
    parent, expected_shards = production_shards()
    indices = tuple(requested_indices)
    if len(indices) != len(set(indices)):
        raise ValueError("requested shard indices contain duplicates")
    records = []
    for index in indices:
        path = output_dir / f"shard-{index:02d}.json"
        with path.open(encoding="utf-8") as source:
            records.append(validate_shard_artifact(json.load(source), index, expected_shards))

    sat_178 = [item for item in records if item["joins"]["178"]["conclusion"] == "SAT"]
    calibrated = all(item["positive_control_179"] == "VALIDATED_SAT" for item in records)
    exact_179 = all(
        (item["joins"]["179"].get("validation") or {}).get("u_count") == 179
        for item in records
    )
    full_coverage = set(indices) == set(range(EXPECTED_SHARD_COUNT)) and len(indices) == 21
    if sat_178:
        conclusion = "SAT"
    elif full_coverage and calibrated:
        conclusion = "UNSAT_IN_LANGUAGE"
    elif full_coverage:
        conclusion = "UNSAT_NOT_CALIBRATED"
    else:
        conclusion = "NO_SAT_IN_REQUESTED_SHARDS"

    def lane_sum(path: Sequence[str]) -> int:
        total = 0
        for item in records:
            value = item
            for key in path:
                value = value[key]
            total += value
        return total

    words = tuple(tuple(item.metadata["operation_word"]) for item in expected_shards)
    aggregate = {
        "schema": AGGREGATE_SCHEMA,
        "completion": True,
        "conclusion": conclusion,
        "requested_indices": list(indices),
        "full_21_shard_coverage": full_coverage,
        "all_requested_179_controls_validated_sat": calibrated,
        "all_requested_179_controls_exactly_179_u": exact_179,
        "operation_words": [list(words[index]) for index in indices],
        "all_operation_words_hash": _words_hash(words),
        "parent_schedule_seam_path_count": parent.complete_path_count,
        "sums_are_lane_schedule_sums_not_distinct_pattern_counts": True,
        "lane_schedule_sums": {
            "seam_paths": lane_sum(("seam_path_count",)),
            "top_frontier_states": lane_sum(("frontiers", "top_states")),
            "bottom_frontier_states": lane_sum(("frontiers", "bottom_states")),
            "join_179_candidate_state_pairs": lane_sum(
                ("joins", "179", "join_stats", "candidate_state_pairs")
            ),
            "join_178_candidate_state_pairs": lane_sum(
                ("joins", "178", "join_stats", "candidate_state_pairs")
            ),
            "join_179_connected_pairs": lane_sum(
                ("joins", "179", "join_stats", "connected_pairs")
            ),
            "join_178_connected_pairs": lane_sum(
                ("joins", "178", "join_stats", "connected_pairs")
            ),
            "join_179_scope_pruned_pairs": lane_sum(
                ("joins", "179", "join_stats", "scope_pruned_pairs")
            ),
            "join_178_scope_pruned_pairs": lane_sum(
                ("joins", "178", "join_stats", "scope_pruned_pairs")
            ),
            "join_179_cost_pruned_pairs": lane_sum(
                ("joins", "179", "join_stats", "cost_pruned_pairs")
            ),
            "join_178_cost_pruned_pairs": lane_sum(
                ("joins", "178", "join_stats", "cost_pruned_pairs")
            ),
            "join_179_cost_feasible_pairs": lane_sum(
                ("joins", "179", "join_stats", "merged_pairs")
            ),
            "join_178_cost_feasible_pairs": lane_sum(
                ("joins", "178", "join_stats", "merged_pairs")
            ),
            "join_179_cache_hits": lane_sum(
                ("joins", "179", "join_stats", "cache_hits")
            ),
            "join_178_cache_hits": lane_sum(
                ("joins", "178", "join_stats", "cache_hits")
            ),
            "join_179_merge_evaluations": lane_sum(
                ("joins", "179", "join_stats", "merge_evaluations")
            ),
            "join_178_merge_evaluations": lane_sum(
                ("joins", "178", "join_stats", "merge_evaluations")
            ),
        },
        "shards": [
            {
                "index": item["operation_word_index"],
                "operation_word_hash": item["operation_word_hash"],
                "seam_path_count": item["seam_path_count"],
                "positive_control_179": item["positive_control_179"],
                "conclusion_178": item["joins"]["178"]["conclusion"],
            }
            for item in records
        ],
    }
    if write:
        write_result(output_dir / "aggregate.json", aggregate)
    return aggregate


def parse_shards(specification: str | None) -> tuple[int, ...]:
    """Parse comma-separated indices and inclusive ranges."""
    if not specification:
        return tuple(range(EXPECTED_SHARD_COUNT))
    selected = set()
    for part in specification.split(","):
        bounds = part.strip().split("-", 1)
        start = int(bounds[0])
        stop = int(bounds[-1])
        if not 0 <= start <= stop < EXPECTED_SHARD_COUNT:
            raise ValueError(f"invalid shard range: {part}")
        selected.update(range(start, stop + 1))
    return tuple(sorted(selected))


def _remove_stale_temporaries(output_dir: Path) -> None:
    for path in output_dir.glob(".shard-*.json.*"):
        path.unlink()
    for path in output_dir.glob(".aggregate.json.*"):
        path.unlink()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workers", type=int, default=8)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--resume", action="store_true")
    parser.add_argument("--shards", help="indices/ranges, for example 0-3,8,12-14")
    parser.add_argument("--cut", type=int, default=8)
    args = parser.parse_args()
    if args.workers < 1 or not 1 <= args.cut < 17:
        parser.error("workers must be positive and cut must be between 1 and 16")
    try:
        requested = parse_shards(args.shards)
    except ValueError as error:
        parser.error(str(error))
    args.output_dir.mkdir(parents=True, exist_ok=True)
    if args.resume:
        _remove_stale_temporaries(args.output_dir)

    _, expected = production_shards()
    pending = []
    for index in requested:
        path = args.output_dir / f"shard-{index:02d}.json"
        if args.resume and path.exists():
            try:
                with path.open(encoding="utf-8") as source:
                    validate_shard_artifact(json.load(source), index, expected)
                continue
            except (OSError, ValueError, json.JSONDecodeError):
                path.unlink()
        pending.append(index)

    if pending:
        with ProcessPoolExecutor(max_workers=args.workers) as executor:
            futures = {
                executor.submit(run_shard, index, args.output_dir, args.cut): index
                for index in pending
            }
            for future in as_completed(futures):
                index = futures[future]
                path = future.result()
                print(f"completed shard {index}: {path}", flush=True)
    aggregate = aggregate_artifacts(args.output_dir, requested)
    print(json.dumps(aggregate, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
