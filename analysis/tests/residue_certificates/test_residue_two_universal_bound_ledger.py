from __future__ import annotations

import json
import unittest

from analysis.residue_certificates.residue_two_universal_bound_ledger import (
    DEFAULT_OUTPUT,
    build_ledger,
    curvature_lower_bound,
    old_baseline,
    verify_baseline_algebra,
)
from analysis.tests._support import migrated_artifact


class ResidueTwoUniversalBoundLedgerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.fresh = build_ledger()
        cls.cached = migrated_artifact(json.loads(DEFAULT_OUTPUT.read_text()))

    def test_cached_ledger_regenerates_exactly(self) -> None:
        self.assertEqual(self.fresh, self.cached)

    def test_width_independent_baseline_algebra(self) -> None:
        for k in range(1, 10_000):
            n = 3 * k + 2
            record = verify_baseline_algebra(n)
            self.assertEqual(record["q_old"], old_baseline(n))
            self.assertEqual(curvature_lower_bound(n, 5), old_baseline(n))

    def test_complete_scope_is_not_promoted_to_arbitrary_width(self) -> None:
        scope = self.fresh["scope"]
        self.assertEqual(scope["complete_operational_widths"], [5, 8])
        self.assertEqual(scope["complete_attachment_skeleton_widths"], [5, 8])
        self.assertFalse(scope["arbitrary_width_baseline_proved"])
        self.assertFalse(scope["arbitrary_width_extra_unit_proved"])
        self.assertEqual(
            {n: item["minimum_charged_curvature"] for n, item in self.fresh["complete_finite_certificates"].items()},
            {"5": 5, "8": 5},
        )

    def test_n11_silent_carrier_gap_is_a_required_falsifier(self) -> None:
        gap = self.fresh["n11_silent_carrier_falsifier"]
        self.assertEqual(gap["charged_curvature"], 5)
        self.assertEqual(gap["contiguous_support_failure_rows"], [8])
        self.assertEqual(gap["occupied_groups"], [1, 3])
        self.assertEqual(gap["silent_packet"], [2])
        self.assertEqual(gap["hull_carrier_failure_rows"], [])
        self.assertEqual(gap["maximum_face_cut_open_width"], 1)

    def test_n17_extra_unit_is_terminal_attachment_debt(self) -> None:
        debt = self.fresh["n17_attachment_debt"]
        self.assertEqual(debt["survivors_two_cells_before_terminal"], 20)
        self.assertEqual(debt["survivor_attachment_debt"], 2)
        self.assertEqual(debt["survivor_merge_capacity_histogram"], {"0": 2, "1": 18})
        self.assertEqual(debt["survivors_with_accepted_suffix"], 0)
        self.assertEqual((debt["minimum_u"], debt["extra_over_old_baseline"]), (179, 1))
        self.assertEqual(
            debt["positive_control"],
            {
                "u_count": 179,
                "hinge_debt": 1,
                "remaining_u_budget": 1,
                "merge_capacity": 1,
                "accepted_suffixes": 1,
            },
        )

    def test_attachment_skeleton_separates_theorem_and_conjecture(self) -> None:
        skeleton = self.fresh["attachment_skeleton"]
        self.assertEqual(skeleton["old_4_3_9_status"], "not-topological-and-false-on-affine-A23")
        self.assertEqual(
            skeleton["A23_old_signature"],
            {
                "maximum_repeated_components": 5,
                "maximum_cyclic_runs_per_component": 3,
                "maximum_compressed_runs": 12,
            },
        )
        self.assertEqual(skeleton["complete_equality"]["5"]["maximum_branch_cost"], 0)
        self.assertEqual(skeleton["complete_equality"]["8"]["maximum_branch_cost"], 1)
        self.assertEqual(skeleton["n11_silent_row8"]["branch_cost"], 1)
        self.assertGreater(skeleton["n11_silent_row8"]["silent_face_slots"], 0)
        self.assertIn("proved", skeleton["theorem_boundary"])
        self.assertIn("conjectured", skeleton["theorem_boundary"])

    def test_affine_skeleton_growth_is_not_promoted_to_theorem(self) -> None:
        growth = self.fresh["attachment_skeleton"]["affine_branch_growth"]
        self.assertEqual(growth["A23"], {"charged_curvature": 14, "maximum_branch_cost": 4})
        self.assertIn(
            "conjectural",
            " ".join(self.fresh["limitations"]),
        )

    def test_cap_merge_potential_supports_five_but_not_n17_extra(self) -> None:
        potential = self.fresh["cap_merge_potential"]
        self.assertEqual(
            potential["training"],
            {
                "complete_widths": [5, 8],
                "feature_states": 133,
                "concrete_transitions": 588,
                "distinct_constraints": 268,
                "terminal_constant": 5,
                "slack_histogram": {"0": 588},
            },
        )
        self.assertTrue(
            all(
                not item["direct_heldout_certificate"]
                for item in potential["heldout_fixed_paths"].values()
            )
        )
        self.assertEqual(potential["n17_baseline"]["available_slack"], 3)
        self.assertIn("not supported", potential["conclusion"]["n17_extra_unit"])
        self.assertEqual(
            potential["n17_terminal_unpayable_debt"]["u178_survivor_deficit_histogram"],
            {"1": 18, "2": 2},
        )

    def test_persistent_debt_replaces_suffix_capacity_in_finite_scope(self) -> None:
        persistent = self.fresh["persistent_debt"]
        self.assertFalse(persistent["local_capacity"]["suffix_enumeration_used"])
        self.assertEqual(persistent["min_plus"]["terminal_constant"], 5)
        self.assertEqual(set(persistent["min_plus"]["slack_histogram"]), {"0"})
        self.assertEqual(
            persistent["n17_terminal"]["u178_unpayable_debt_histogram"],
            {"1": 18, "2": 2},
        )
        self.assertEqual(
            persistent["n17_terminal"]["u179_control"]["unpayable_debt"], 0
        )
        self.assertIn("open", persistent["finite_language"]["coverage_status"])

    def test_missing_lemma_mentions_low_curvature_and_silent_passage(self) -> None:
        lemma = self.fresh["smallest_missing_coverage_lemma"]
        self.assertIn("K(U)<=5", lemma["statement"])
        self.assertIn("silently", lemma["statement"])
        self.assertIn("min-plus weight 5", lemma["statement"])

    def test_invalid_baseline_arguments_are_rejected(self) -> None:
        for n in (2, 6, 7):
            with self.subTest(n=n), self.assertRaises(ValueError):
                old_baseline(n)


if __name__ == "__main__":
    unittest.main()
