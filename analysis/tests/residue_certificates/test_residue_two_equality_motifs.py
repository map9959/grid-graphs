from __future__ import annotations

import json
import os
import unittest


from analysis.residue_certificates.residue_two_equality_motifs import (
    EventWord,
    IntervalEvent,
    build_artifact,
    canonical_rooted_partition,
    decode_event_word,
    encode_event_word,
    event_metrics,
    motif_key,
)
from analysis.tiles.tile_grammar import FrontierState
from analysis._paths import analysis_path
from analysis.tests._support import migrated_artifact


ARTIFACT = analysis_path("residue_two_equality_motifs.json")


class ResidueTwoEqualityMotifTests(unittest.TestCase):
    def test_event_word_is_lossless_and_packetized(self) -> None:
        partition = (7, 2, 2, 9, 7, 9, 2, 4)
        canonical = canonical_rooted_partition(partition)
        word = encode_event_word(8, partition)
        self.assertEqual(tuple(map(len, word.packets)), (3, 3, 1))
        self.assertEqual(decode_event_word(word), canonical)
        self.assertEqual(
            tuple(event.role for packet in word.packets for event in packet),
            ("open", "carry", "open", "single", "close", "close", "single"),
        )

    def test_event_validation_and_metrics(self) -> None:
        word = encode_event_word(8, (0, 1, 2, 1, 2, 3, 3, 0))
        metrics = event_metrics(word)
        self.assertEqual(metrics["max_stack_depth"], 2)
        self.assertEqual(metrics["carry_widths"], (1, 0))
        self.assertEqual(metrics["component_spans"], (1, 2, 3, 3))
        broken = EventWord(8, 0, ((IntervalEvent(1, "close"),) * 7,))
        with self.assertRaises(ValueError):
            decode_event_word(broken)

    def test_candidate_hierarchy_and_unknown_candidate(self) -> None:
        state = FrontierState(8, 3, 0, (0, 1, 1, 1, 2, 2, 2, 0), 0, 0)
        run_length = motif_key(state, "run_length")
        affine = motif_key(state, "affine")
        self.assertEqual(run_length[:2], affine[:2])
        self.assertIn("2+", repr(affine))
        with self.assertRaises(ValueError):
            motif_key(state, "unknown")

    def test_cached_artifact_has_declared_complete_and_fixed_coverage(self) -> None:
        artifact = migrated_artifact(json.loads(ARTIFACT.read_text()))
        self.assertEqual(artifact["scope"]["complete_equality_corridors"], [5, 8])
        self.assertEqual(artifact["scope"]["fixed_equality_witnesses"], [11, 14])
        self.assertEqual(artifact["scope"]["near_equality_control"], {"width": 17, "u_count": 179})
        self.assertEqual(artifact["coverage"]["complete_continuation_states"], 325)
        self.assertEqual(artifact["coverage"]["fixed_trace_states_without_complete_continuation_claim"], 45)
        self.assertEqual(artifact["coverage"]["states"], 370)
        self.assertEqual(artifact["coverage"]["lossless_event_word_round_trips"], 370)
        self.assertEqual(
            artifact["sources"]["n5-complete-equality-corridor"]["states"], 117
        )
        self.assertEqual(
            artifact["sources"]["n8-complete-equality-corridor"]["states"], 208
        )
        for candidate in ("run_length", "affine"):
            report = artifact["continuation_collisions"][candidate]
            self.assertEqual(
                tuple(
                    report[field]
                    for field in (
                        "keys",
                        "merged_groups",
                        "collision_groups",
                        "cross_width_collision_groups",
                    )
                ),
                (171, 52, 45, 1),
            )
            self.assertTrue(report["collisions"])

    @unittest.skipUnless(os.environ.get("GRID_GRAPHS_SLOW"), "slow exact regeneration")
    def test_cached_artifact_regenerates_exactly(self) -> None:
        self.assertEqual(build_artifact(), migrated_artifact(json.loads(ARTIFACT.read_text())))


if __name__ == "__main__":
    unittest.main()
