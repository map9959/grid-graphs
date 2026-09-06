from __future__ import annotations

import unittest

from analysis.residue_geometry.check_residue_two_zero_sparse_rail_ladder import (
    HARD_DESCRIPTOR_BOUND,
    SCHEMA,
    analyze_k,
    build_report,
    iter_descriptors,
)


class ResidueTwoZeroSparseRailLadderTests(unittest.TestCase):
    def test_declared_phase_grammar_has_hard_bound(self) -> None:
        descriptors = list(iter_descriptors())
        self.assertEqual(HARD_DESCRIPTOR_BOUND, 576)
        self.assertEqual(len(descriptors), HARD_DESCRIPTOR_BOUND)

    def test_k7_k8_k9_are_complete_obstructions(self) -> None:
        for k in (7, 8, 9):
            with self.subTest(k=k):
                record = analyze_k(k)
                self.assertEqual(record["status"], "complete_grammar_obstruction")
                self.assertTrue(all(record["checks"].values()))
                self.assertEqual(record["enumeration"]["materializations_checked"], 576)
                self.assertEqual(record["obstruction"]["minimum_star_intersection"], 3)
                self.assertEqual(record["obstruction"]["survivors"], 0)

    def test_best_materializations_are_exact_and_local(self) -> None:
        for k in (7, 8, 9):
            best = analyze_k(k)["best_materialization"]
            self.assertEqual(best["replacement_count"], 10 * k - 4)
            self.assertEqual(best["forced_count"], 3 * k * k + 7 * k)
            self.assertTrue(best["checks"]["unit_cells_valid"])
            self.assertTrue(best["checks"]["components_straight"])
            self.assertTrue(best["checks"]["stable_count_interface"])
            self.assertFalse(best["checks"]["singleton_star_intersections"])
            self.assertFalse(best["checks"]["incidence_tree"])
            self.assertFalse(best["checks"]["forced_forest"])

    def test_report_closes_fixed_two_layer_branch(self) -> None:
        report = build_report()
        self.assertEqual(report["schema"], SCHEMA)
        self.assertEqual(report["status"], "complete_grammar_obstruction")
        self.assertFalse(
            report["branch_decision"]["continue_fixed_two_layer_zero_cap_splice"]
        )
        self.assertEqual(report["symbolic_obstruction"]["stable_count_gain"], 10)


if __name__ == "__main__":
    unittest.main()
