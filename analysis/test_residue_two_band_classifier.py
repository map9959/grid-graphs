from __future__ import annotations

import json
import os
import unittest
from pathlib import Path

from diagonal_patterns import residue_two_affine_pattern, residue_two_explicit_pattern
from residue_two_band_classifier import (
    boundary_role,
    build_artifact,
    classify_masks,
)
from tile_grammar import row_mask


ARTIFACT = Path(__file__).with_name("residue_two_band_classifier.json")


class ResidueTwoBandClassifierTests(unittest.TestCase):
    def test_fixed_witnesses_replay_every_sliding_and_aligned_window(self) -> None:
        for n, rows in (
            (11, residue_two_explicit_pattern(11)),
            (14, residue_two_explicit_pattern(14)),
            (17, residue_two_affine_pattern(17)),
        ):
            with self.subTest(n=n):
                observations = classify_masks(tuple(map(row_mask, rows)))
                self.assertEqual(len(observations), n - 2)
                self.assertEqual(
                    sum("aligned" in item.window_kinds for item in observations),
                    (n - 1) // 3,
                )
                self.assertEqual(observations[0].boundary_role, "top")
                self.assertEqual(observations[-1].boundary_role, "bottom")
                for item in observations:
                    self.assertEqual(item.weight, 3 * item.d_u - 2 * item.rank_delta - 3)
                    self.assertEqual(
                        item.attachment_debt_delta,
                        item.attachment_debt_after - item.attachment_debt_before,
                    )
                    self.assertEqual(len(item.out_merges), 3)
                    self.assertEqual(len(item.packet_offsets.u), 3)
                    self.assertEqual(len(item.packet_offsets.vertical_edges), 3)

    def test_boundary_roles_validate_window(self) -> None:
        self.assertEqual(boundary_role(8, 0), "top")
        self.assertEqual(boundary_role(8, 2), "interior")
        self.assertEqual(boundary_role(8, 5), "bottom")
        with self.assertRaisesRegex(ValueError, "does not fit"):
            boundary_role(8, 6)

    def test_cached_artifact_has_complete_source_and_graph_provenance(self) -> None:
        artifact = json.loads(ARTIFACT.read_text())
        self.assertEqual(artifact["sources"]["n5-exact-corridor"]["paths"], 242)
        self.assertEqual(artifact["sources"]["n8-exact-corridor"]["paths"], 704)
        self.assertEqual(artifact["sources"]["n5-exact-corridor"]["sliding_windows"], 726)
        self.assertEqual(artifact["sources"]["n8-exact-corridor"]["sliding_windows"], 4224)
        self.assertEqual(artifact["census"]["sliding_window_observations"], 4986)
        self.assertEqual(artifact["census"]["normalized_classes"], 463)
        self.assertTrue(artifact["census"]["any_complete_normalized_class_recurs"])
        self.assertEqual(
            [item["widths"] for item in artifact["recurring_complete_normalized_classes"]],
            [[5, 8], [8, 17], [14, 17]],
        )
        self.assertIn("provenance", artifact["observed_graph"])
        self.assertIn("warning", artifact["observed_graph"])
        self.assertEqual(artifact["observed_graph"]["nontrivial_strong_components"], 14)

    @unittest.skipUnless(os.environ.get("GRID_GRAPHS_SLOW"), "slow exact regeneration")
    def test_cached_artifact_regenerates_exactly(self) -> None:
        self.assertEqual(build_artifact(), json.loads(ARTIFACT.read_text()))


if __name__ == "__main__":
    unittest.main()
