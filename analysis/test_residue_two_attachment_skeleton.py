from __future__ import annotations

import json
import os
import unittest

from residue_two_attachment_skeleton import (
    DEFAULT_OUTPUT,
    alternating_component_pair,
    attachment_skeleton,
    build_artifact,
    nested_noncrossing_word,
)


class ResidueTwoAttachmentSkeletonTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.artifact = json.loads(DEFAULT_OUTPUT.read_text())

    def test_unconditional_occurrence_bounds(self) -> None:
        for word in (
            (),
            (0,),
            (0, 0, 1, 0, 2, 2),
            nested_noncrossing_word(12),
        ):
            skeleton = attachment_skeleton(word)
            self.assertLessEqual(skeleton.branching_components, skeleton.branch_cost)
            self.assertLessEqual(
                skeleton.branch_cost,
                skeleton.port_occurrences - skeleton.ported_components,
            )

    def test_alternation_detector_separates_crossing_and_nested_words(self) -> None:
        self.assertEqual(alternating_component_pair((0, 1, 0, 1)), (0, 1))
        self.assertIsNone(alternating_component_pair(nested_noncrossing_word(20)))

    def test_old_4_3_9_claim_is_falsified_by_a23(self) -> None:
        report = self.artifact["old_4_3_9_falsification"]
        self.assertEqual(report["status"], "not-topological-and-false-on-affine-A23")
        self.assertEqual(
            report["A23_observed"],
            {
                "maximum_repeated_components": 5,
                "maximum_cyclic_runs_per_component": 3,
                "maximum_compressed_runs": 12,
            },
        )
        self.assertGreater(
            report["nested_noncrossing_family"]["12"]["branching_components"], 4
        )

    def test_complete_and_fixed_equality_branch_cost_is_at_most_one(self) -> None:
        complete = self.artifact["complete_small_equality"]
        self.assertEqual(complete["5"]["maximum_branch_cost_histogram"], {"0": 242})
        self.assertEqual(complete["8"]["maximum_branch_cost_histogram"], {"0": 576, "1": 128})
        self.assertTrue(
            all(item["maximum_branch_cost"] <= 1 for item in complete.values())
        )
        self.assertTrue(
            all(
                item["maximum_branch_cost"] <= 1
                for item in self.artifact["fixed_equality_controls"].values()
            )
        )

    def test_affine_controls_expose_linear_branch_growth(self) -> None:
        affine = self.artifact["affine_surplus_controls"]
        self.assertEqual(
            [affine[f"A{n}"]["maximum_branch_cost"] for n in range(17, 42, 3)],
            list(range(2, 11)),
        )
        for item in affine.values():
            self.assertEqual(
                3 * item["maximum_branch_cost"], item["charged_curvature"] - 2
            )

    def test_n11_silent_gap_retains_positive_branch_cost(self) -> None:
        row8 = self.artifact["n11_silent_frontier_history"][8]
        self.assertEqual(row8["completed_rows"], 8)
        self.assertEqual(row8["branch_cost"], 1)
        self.assertGreater(row8["silent_face_slots"], 0)

    def test_simple_row_local_potentials_are_exactly_falsified(self) -> None:
        for case in self.artifact["complete_small_equality"].values():
            for result in case["local_candidate_inequalities"].values():
                self.assertLess(result["minimum_slack"], 0)
                self.assertIsNotNone(result["counterexample"])

    @unittest.skipUnless(
        os.environ.get("GRID_GRAPHS_REGENERATE"), "slow complete n=5,8 regeneration"
    )
    def test_complete_artifact_regenerates(self) -> None:
        self.assertEqual(build_artifact(regenerate_complete=True), self.artifact)


if __name__ == "__main__":
    unittest.main()
