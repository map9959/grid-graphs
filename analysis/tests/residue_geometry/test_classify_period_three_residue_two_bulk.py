from __future__ import annotations

import json

import unittest

from analysis.residue_geometry.classify_period_three_residue_two_bulk import (
    boundary_maximum,
    build_report,
    forced_forest,
    gap_grammar_maximum,
    materialize,
)
from analysis._paths import analysis_path
from analysis.tests._support import migrated_artifact


ARTIFACT = analysis_path("period_three_residue_two_bulk.json")


class PeriodThreeResidueTwoBulkTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.report = build_report()

    def test_complete_mask_and_orbit_classification(self) -> None:
        bulk = self.report["bulk_classification"]
        self.assertEqual(self.report["scope"]["masks_enumerated"], 512)
        self.assertEqual(self.report["scope"]["three_center_masks"], 84)
        self.assertEqual(bulk["unit_cell_survivors"], 6)
        self.assertEqual(bulk["symbolic_quotient_survivors"], 6)
        self.assertEqual(bulk["symmetry_phase_orbits"], 1)

    def test_symbolic_criterion_agrees_with_large_open_boxes(self) -> None:
        for survivor in self.report["bulk_classification"]["survivors"]:
            self.assertTrue(survivor["quotient"]["lift_is_forest"])
            for repetitions in (2, 3, 5, 8, 13):
                side = 3 * repetitions
                self.assertTrue(forced_forest(side, side, materialize(survivor["mask"], repetitions)))

    def test_boundary_hard_bound_and_stable_increment(self) -> None:
        self.assertEqual([boundary_maximum(7, phase) for phase in range(3)], [37, 30, 37])
        self.assertEqual([gap_grammar_maximum(3 * k + 2)["maximum"] for k in (7, 8, 9)], [8, 9, 10])
        self.assertEqual(self.report["boundary_grammar"]["maximum_total"], "3k^2+5k+2")
        self.assertEqual(self.report["target_decision"]["maximum_deficit"], "2k-2")
        self.assertFalse(self.report["target_decision"]["attainable"])

    def test_k_7_8_9_maximizers(self) -> None:
        expected = {7: [37, 30, 37], 8: [42, 34, 42], 9: [47, 38, 47]}
        for record in self.report["validation"]:
            phases = record["phases"]
            self.assertEqual([item["boundary_count"] for item in phases], expected[record["k"]])
            self.assertTrue(all(item["straight_components"] and item["forced_forest"] for item in phases))

    def test_artifact_is_current(self) -> None:
        self.assertEqual(migrated_artifact(json.loads(ARTIFACT.read_text())), self.report)


if __name__ == "__main__":
    unittest.main()
