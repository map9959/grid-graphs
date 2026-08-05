from __future__ import annotations

import json
import os
import unittest
from pathlib import Path

from residue_two_structural_defect_gap import CATEGORIES, build_artifact


ARTIFACT = Path(__file__).with_name("residue_two_structural_defect_gap.json")


class ResidueTwoStructuralDefectGapTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.artifact = json.loads(ARTIFACT.read_text())

    @unittest.skipUnless(os.environ.get("GRID_GRAPHS_SLOW"), "slow exact regeneration")
    def test_exact_regeneration(self) -> None:
        self.assertEqual(build_artifact(), self.artifact)

    def test_scope_minima_and_counts_are_pinned(self) -> None:
        artifact = self.artifact
        self.assertEqual(artifact["scope"]["complete_equality_corridors"], [5, 8])
        self.assertFalse(artifact["scope"]["arbitrary_width_coverage_claimed"])
        self.assertEqual(
            set(artifact["state_defects"]) | set(artifact["absent_categories"]["states"]),
            set(CATEGORIES),
        )
        self.assertEqual(
            set(artifact["transition_created_defects"])
            | set(artifact["absent_categories"]["creating_transitions"]),
            set(CATEGORIES),
        )
        expected = {
            "support_hole_count": (3, 101, 3, 438),
            "concurrent_packet_carriers": (3, 16, 3, 28),
            "maximum_face_cut_width_gt_1": (3, 31, 3, 55),
            "forbidden_motif_010": (3, 286, 3, 2112),
            "forbidden_motif_121": (3, 36, 3, 117),
            "combined_grammar_rejection": (3, 439, 3, 2297),
        }
        actual = {
            name: (
                artifact["state_defects"][name]["minimum_slack"],
                artifact["state_defects"][name]["states"],
                artifact["transition_created_defects"][name]["minimum_slack"],
                artifact["transition_created_defects"][name]["creating_transitions"],
            )
            for name in artifact["state_defects"].keys()
            & artifact["transition_created_defects"].keys()
        }
        self.assertEqual(actual, expected)

    def test_witness_values_are_exact_and_positive(self) -> None:
        for section, slack_field in (
            ("state_defects", "reduced_slack"),
            ("transition_created_defects", "complete_path_edge_slack"),
        ):
            for report in self.artifact[section].values():
                witness = report["witness"]
                self.assertEqual(witness[slack_field], report["minimum_slack"])
                self.assertGreater(witness[slack_field], 0)
                expected = witness["forward"] + witness["backward"] - witness["minimum"]
                if section == "transition_created_defects":
                    expected += witness["edge_weight"]
                self.assertEqual(witness[slack_field], expected)
                width = witness["width"]
                self.assertEqual(len(witness["previous_mask_rendered"]), width + 2)
                key = (
                    witness["structural_key"]
                    if "structural_key" in witness
                    else witness["incoming_structural_key"]
                )
                self.assertEqual(witness["row"], key[0])


if __name__ == "__main__":
    unittest.main()
