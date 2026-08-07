from __future__ import annotations

import json
import os
import unittest

from residue_two_cap_merge_potential import DEFAULT_OUTPUT, build_artifact


class ResidueTwoCapMergePotentialTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.artifact = json.loads(DEFAULT_OUTPUT.read_text())

    @unittest.skipUnless(os.environ.get("GRID_GRAPHS_SLOW"), "slow exact regeneration")
    def test_cached_artifact_regenerates(self) -> None:
        self.assertEqual(build_artifact(), self.artifact)

    def test_complete_training_certificate_is_exact_and_tight(self) -> None:
        certificate = self.artifact["training_certificate"]
        self.assertEqual(certificate["terminal_constant"], 5)
        self.assertEqual(certificate["slack_histogram"], {"0": 588})
        self.assertEqual(
            certificate["complete_source_census"],
            {
                "n5-complete": {
                    "feature_states": 54,
                    "transitions": 220,
                    "terminal_features": 5,
                },
                "n8-complete": {
                    "feature_states": 90,
                    "transitions": 368,
                    "terminal_features": 5,
                },
            },
        )
        self.assertLessEqual(certificate["features"], 140)

    def test_silent_support_is_not_a_feature_requirement(self) -> None:
        policy = self.artifact["feature"]["silent_carrier_policy"]
        self.assertIn("no contiguous-support bit", policy)
        self.assertIn("silent gaps", policy)

    def test_fixed_width_paths_are_extensions_not_heldout_coverage(self) -> None:
        for name, control in self.artifact["heldout_fixed_paths"].items():
            with self.subTest(name=name):
                self.assertEqual(control["total_weight"], 5)
                self.assertFalse(control["direct_heldout_certificate"])
                self.assertLess(control["states_known_to_training"], control["states"])
        extension = self.artifact["fixed_path_extension_certificate"]
        self.assertEqual(set(extension["slack_histogram"]), {"0"})

    def test_cap_and_merge_features_are_material(self) -> None:
        ablation = self.artifact["feature_ablation"]
        self.assertGreater(ablation["without_cap_phase"]["incompatible_groups"], 0)
        self.assertGreater(
            ablation["without_merge_capacity_surplus"]["incompatible_groups"], 0
        )

    def test_n17_baseline_has_three_slack_but_not_extra_unit(self) -> None:
        control = self.artifact["n17_baseline_extension"]
        self.assertEqual(control["path_total_weight"], 8)
        self.assertEqual(control["baseline_terminal_constant"], 5)
        self.assertEqual(control["total_available_slack"], 3)
        self.assertIn("not supported", self.artifact["result"]["n17_extra_unit"])

    def test_n17_terminal_unpayable_debt_separates_failed_states(self) -> None:
        terminal = self.artifact["n17_terminal_debt"]
        self.assertEqual(terminal["u178_survivor_deficit_histogram"], {"1": 18, "2": 2})
        self.assertTrue(terminal["u178_all_positive"])
        self.assertEqual(terminal["u179_positive_control_deficit"], 0)


if __name__ == "__main__":
    unittest.main()
