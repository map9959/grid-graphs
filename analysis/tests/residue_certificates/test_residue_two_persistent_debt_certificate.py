from __future__ import annotations

import json
import os
import unittest

from analysis.residue_certificates.residue_two_persistent_debt_certificate import (
    DEFAULT_OUTPUT,
    build_artifact,
    maximum_terminal_row_edges,
)
from analysis.tests._support import migrated_artifact


class ResidueTwoPersistentDebtCertificateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.artifact = migrated_artifact(json.loads(DEFAULT_OUTPUT.read_text()))

    @unittest.skipUnless(os.environ.get("GRID_GRAPHS_SLOW"), "slow exact regeneration")
    def test_cached_artifact_regenerates(self) -> None:
        self.assertEqual(build_artifact(), self.artifact)

    def test_terminal_row_edge_dp_is_exact_on_small_controls(self) -> None:
        self.assertEqual(maximum_terminal_row_edges(3, 0b111, 0), 0)
        self.assertEqual(maximum_terminal_row_edges(3, 0b111, 1), 1)
        self.assertEqual(maximum_terminal_row_edges(3, 0b111, 2), 3)
        self.assertEqual(maximum_terminal_row_edges(3, 0, 3), 2)

    def test_complete_history_languages_have_no_unpayable_debt(self) -> None:
        census = self.artifact["complete_history_census"]
        self.assertEqual(set(census), {"n5-complete", "n8-complete"})
        self.assertGreater(census["n5-complete"]["histories"], 100)
        self.assertGreater(census["n8-complete"]["histories"], 300)
        certificate = self.artifact["min_plus_certificate"]
        self.assertEqual(certificate["terminal_constant"], 5)
        self.assertEqual(set(certificate["slack_histogram"]), {"0"})

    def test_fixed_equality_controls_survive_local_bound(self) -> None:
        self.assertEqual(
            set(self.artifact["fixed_controls"]), {"n11-fixed", "n11-silent", "n14-fixed"}
        )
        for control in self.artifact["fixed_controls"].values():
            self.assertEqual(control["total_weight"], 5)
            self.assertEqual(control["maximum_unpayable_debt"], 0)

    def test_n17_terminal_separation_uses_no_suffix_acceptance(self) -> None:
        terminal = self.artifact["n17_terminal_separation"]
        self.assertEqual(terminal["u178_states_checked"], 20)
        self.assertEqual(terminal["u178_unpayable_debt_histogram"], {"1": 18, "2": 2})
        self.assertEqual(terminal["u179_control"]["unpayable_debt"], 0)
        self.assertFalse(self.artifact["local_capacity_theorem"]["suffix_enumeration_used"])

    def test_finite_theorem_is_not_global_coverage(self) -> None:
        language = self.artifact["low_curvature_hull_language"]
        self.assertIn("explicitly enumerated", language["finite_theorem"])
        self.assertIn("open", language["coverage_status"])
        self.assertEqual(self.artifact["result"]["global_k_ge_5"], "conjectural pending low-curvature hull-language coverage")


if __name__ == "__main__":
    unittest.main()
