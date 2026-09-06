from __future__ import annotations

import json
import os
import unittest

from analysis.residue_certificates.residue_two_first_defect_certificate import DEFAULT_OUTPUT, build_artifact
from analysis.tests._support import migrated_artifact


class ResidueTwoFirstDefectCertificateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.artifact = migrated_artifact(json.loads(DEFAULT_OUTPUT.read_text()))

    def test_scope_is_explicitly_finite_and_oracle_based(self) -> None:
        scope = self.artifact["scope"]
        self.assertEqual(scope["widths"], [5, 8])
        self.assertFalse(scope["arbitrary_width_coverage_claimed"])
        self.assertTrue(scope["bounded_symbolic_transition_soundness_proved_for_monitored_edges"])
        self.assertFalse(scope["arbitrary_word_transition_closure_claimed"])
        self.assertFalse(scope["universal_terminal_bound_claimed"])

    def test_first_defect_and_clean_terminal_minima(self) -> None:
        n5 = self.artifact["widths"]["5"]
        n8 = self.artifact["widths"]["8"]
        self.assertEqual(n5["first_state_codec_defect"]["status"], "absent")
        self.assertEqual(n8["first_state_codec_defect"]["minimum_complete_path_curvature"], 8)
        self.assertEqual(n8["first_state_codec_defect"]["gap_above_width_minimum"], 3)
        self.assertEqual(n5["defect_free_terminal"]["minimum_complete_path_curvature"], 5)
        self.assertEqual(n8["defect_free_terminal"]["minimum_complete_path_curvature"], 5)
        for report in (n5, n8):
            self.assertEqual(report["transition_closure_defect"]["status"], "absent")
            self.assertGreater(
                report["transition_closure_defect"]["checked_codec_valid_completable_edges"], 0
            )

    def test_witness_counts_recompute_curvature(self) -> None:
        for n in (5, 8):
            report = self.artifact["widths"][str(n)]
            witnesses = [report["defect_free_terminal"]["witness"]]
            defect = report["first_state_codec_defect"]
            if defect["status"] == "present":
                witnesses.append(defect["witness"])
            for witness in witnesses:
                self.assertEqual(len(witness["row_masks"]), n)
                expected = 3 * witness["u_count"] - 2 * (n - 1) ** 2 - n
                self.assertEqual(witness["curvature"], expected)

    def test_n11_silent_gap_is_not_a_codec_defect(self) -> None:
        control = self.artifact["n11_silent_control"]
        self.assertTrue(control["all_frontiers_codec_valid"])
        self.assertTrue(control["all_bounded_symbolic_transitions_valid"])
        self.assertEqual(control["silent_rows"], [8])

    @unittest.skipUnless(os.environ.get("GRID_GRAPHS_SLOW"), "slow exact regeneration")
    def test_artifact_regenerates_exactly(self) -> None:
        self.assertEqual(build_artifact(), self.artifact)


if __name__ == "__main__":
    unittest.main()
