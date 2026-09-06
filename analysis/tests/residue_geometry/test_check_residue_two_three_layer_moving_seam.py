from __future__ import annotations

import unittest

from analysis.residue_geometry.check_residue_two_three_layer_moving_seam import (
    ARM_WORDS,
    HARD_DESCRIPTOR_BOUND,
    SCHEMA,
    build_report,
    derive_count_ledger,
    iter_arm_words,
)


class ResidueTwoThreeLayerMovingSeamTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.report = build_report()

    def test_count_ledger_precedes_search(self) -> None:
        for k in (7, 8, 9):
            with self.subTest(k=k):
                ledger = derive_count_ledger(k)
                self.assertEqual(ledger["replacement_count"], 10 * k - 4)
                self.assertEqual(ledger["packet_count"], k - 2)
                self.assertEqual(ledger["packet_gain"], 10)
                self.assertEqual(ledger["cap_count"], 16)

    def test_compact_phase_grammar_has_exact_bound(self) -> None:
        self.assertEqual(ARM_WORDS, 162)
        self.assertEqual(len(tuple(iter_arm_words())), ARM_WORDS)
        self.assertEqual(HARD_DESCRIPTOR_BOUND, 104_976)

    def test_requested_widths_have_exact_intersection_obstruction(self) -> None:
        self.assertEqual(self.report["schema"], SCHEMA)
        self.assertEqual(self.report["status"], "complete_grammar_obstruction")
        for record in self.report["records"]:
            with self.subTest(k=record["k"]):
                census = record["enumeration"]
                obstruction = record["capacity_or_intersection"]
                self.assertEqual(census["descriptors_classified"], HARD_DESCRIPTOR_BOUND)
                self.assertEqual(census["bottom_strip_admissible"], 39)
                self.assertEqual(census["right_strip_admissible"], 39)
                self.assertEqual(census["joint_materializations_checked"], 6084)
                self.assertEqual(census["locally_valid"], 4624)
                self.assertEqual(obstruction["minimum_star_intersection_among_local"], 2)
                self.assertEqual(obstruction["survivors"], 0)

    def test_best_local_cases_still_fail_global_gates(self) -> None:
        for record in self.report["records"]:
            best = record["best_materialization"]
            self.assertTrue(best["checks"]["unit_cells_valid"])
            self.assertTrue(best["checks"]["components_straight"])
            self.assertFalse(best["checks"]["singleton_star_intersections"])
            self.assertFalse(best["checks"]["incidence_tree"])
            self.assertFalse(best["checks"]["forced_forest"])

    def test_branch_assessment_requires_new_base(self) -> None:
        assessment = self.report["branch_assessment"]
        self.assertFalse(assessment["stable_candidate"])
        self.assertTrue(assessment["wholly_new_base_required"])


if __name__ == "__main__":
    unittest.main()
