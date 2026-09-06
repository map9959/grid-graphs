from __future__ import annotations

import copy
import json
import tempfile
import unittest
from pathlib import Path

from analysis.searches.run_residue_two_moving_seam_shards import (
    AGGREGATE_SCHEMA,
    SHARD_SCHEMA,
    _words_hash,
    aggregate_artifacts,
    parse_shards,
    production_shards,
    validate_shard_artifact,
)
from analysis.searches.search_residue_two_moving_seam import (
    operation_word_hash,
    write_result,
)
from analysis.tests._support import migrated_artifact


class MovingSeamShardRunnerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.parent, cls.shards = production_shards()
        cls.words = tuple(
            tuple(shard.metadata["operation_word"]) for shard in cls.shards
        )

    def artifact(
        self,
        index: int,
        *,
        seam_paths: int | None = None,
        candidates: int = 3,
        sat_179: bool = True,
        sat_178: bool = False,
    ) -> dict:
        shard = self.shards[index]

        def join(budget: int, sat: bool) -> dict:
            return {
                "u_count": budget,
                "conclusion": "SAT" if sat else "UNSAT_IN_LANGUAGE",
                "complete": True,
                "top_states": 2,
                "bottom_states": 4,
                "join_stats": {
                    "alignment_buckets": 1,
                    "candidate_state_pairs": candidates,
                    "cost_pruned_pairs": 0,
                    "merged_pairs": candidates,
                    "connected_pairs": int(sat),
                    "cache_hits": 0,
                    "merge_evaluations": candidates,
                    "scope_pruned_pairs": 0,
                },
                "witness": ["U"] if sat else None,
                "steps": None,
                "validation": {"accepted": True, "u_count": budget} if sat else None,
                "join_seconds": 0.01,
            }

        word = self.words[index]
        return {
            "schema": SHARD_SCHEMA,
            "completion": True,
            "operation_word_index": index,
            "operation_word": list(word),
            "operation_word_hash": operation_word_hash(word),
            "all_operation_words_hash": _words_hash(self.words),
            "seam_path_count": (
                shard.complete_path_count if seam_paths is None else seam_paths
            ),
            "layer_state_counts": list(shard.layer_state_counts),
            "layer_edge_counts": list(shard.layer_edge_counts),
            "fixed_affine_target_membership": True,
            "scope": {
                "parent_schedule": "affine-one-hold-relocation",
                "source_n": 14,
                "target_n": 17,
                "radius": 1,
                "fixed_rows": [0, 1, 2, 15, 16],
                "boundary_rewrite_budget": 1,
                "u_frontier_limit": 179,
                "join_u_counts": [179, 178],
            },
            "frontiers": {
                "top_states": 2,
                "bottom_states": 4,
                "top_stats": [],
                "bottom_stats": [],
            },
            "joins": {"179": join(179, sat_179), "178": join(178, sat_178)},
            "positive_control_179": (
                "VALIDATED_SAT" if sat_179 else "NOT_VALIDATED_SAT"
            ),
        }

    def test_parse_shards(self) -> None:
        self.assertEqual(parse_shards("0-2,5,2"), (0, 1, 2, 5))
        self.assertEqual(len(parse_shards(None)), 21)
        with self.assertRaises(ValueError):
            parse_shards("20-21")

    def test_artifact_validation_rejects_incomplete_and_tampered_identity(self) -> None:
        valid = self.artifact(0)
        validate_shard_artifact(valid, 0, self.shards)
        for mutation in ("completion", "operation_word", "operation_word_hash"):
            damaged = copy.deepcopy(valid)
            if mutation == "completion":
                damaged[mutation] = False
            elif mutation == "operation_word":
                damaged[mutation] = damaged[mutation][::-1]
            else:
                damaged[mutation] = "tampered"
            with self.assertRaises(ValueError, msg=mutation):
                validate_shard_artifact(damaged, 0, self.shards)

    def test_aggregation_rejects_missing_and_duplicate_requests(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary)
            with self.assertRaises(FileNotFoundError):
                aggregate_artifacts(output, [0], write=False)
            write_result(output / "shard-00.json", self.artifact(0))
            with self.assertRaises(ValueError):
                aggregate_artifacts(output, [0, 0], write=False)

    def test_mocked_full_aggregate_uses_lane_sums_and_calibration(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary)
            for index in range(21):
                write_result(output / f"shard-{index:02d}.json", self.artifact(index))
            aggregate = aggregate_artifacts(output, range(21))
            self.assertEqual(aggregate["schema"], AGGREGATE_SCHEMA)
            self.assertEqual(aggregate["conclusion"], "UNSAT_IN_LANGUAGE")
            self.assertEqual(
                aggregate["lane_schedule_sums"]["seam_paths"], 1274550
            )
            self.assertEqual(
                aggregate["lane_schedule_sums"]["join_178_candidate_state_pairs"],
                63,
            )
            self.assertTrue(
                aggregate["sums_are_lane_schedule_sums_not_distinct_pattern_counts"]
            )
            self.assertEqual(
                aggregate["lane_schedule_sums"]["join_178_cost_feasible_pairs"],
                63,
            )
            self.assertTrue(aggregate["all_requested_179_controls_exactly_179_u"])
            self.assertEqual(
                migrated_artifact(json.loads((output / "aggregate.json").read_text())), aggregate
            )

    def test_aggregate_sat_and_uncalibrated_negative(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary)
            for index in range(21):
                write_result(
                    output / f"shard-{index:02d}.json",
                    self.artifact(index, sat_179=index != 3),
                )
            self.assertEqual(
                aggregate_artifacts(output, range(21), write=False)["conclusion"],
                "UNSAT_NOT_CALIBRATED",
            )
            write_result(output / "shard-03.json", self.artifact(3, sat_178=True))
            self.assertEqual(
                aggregate_artifacts(output, range(21), write=False)["conclusion"],
                "SAT",
            )


if __name__ == "__main__":
    unittest.main()
