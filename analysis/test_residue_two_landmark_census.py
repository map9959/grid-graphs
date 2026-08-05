from __future__ import annotations

import json
import unittest

from residue_two_landmark_census import DEFAULT_OUTPUT, build_artifact


class ResidueTwoLandmarkCensusTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.fresh = build_artifact()

    def test_committed_artifact_reproduces(self) -> None:
        self.assertEqual(json.loads(DEFAULT_OUTPUT.read_text()), self.fresh)

    def test_every_match_has_a_closed_slab_interface(self) -> None:
        for pair in self.fresh["claim"]["pairs"]:
            for match in pair["top_matches"] + pair["bottom_matches"]:
                self.assertEqual(len(match["hidden_attachment_labels"]), 3)
                visible = {item["target_attachment_label"] for item in match["component_deltas"]}
                self.assertTrue(set(match["hidden_attachment_labels"]) <= visible)
                self.assertEqual(
                    [item["source_label"] for item in match["component_deltas"]],
                    list(range(len(match["component_deltas"]))),
                )


if __name__ == "__main__":
    unittest.main()
