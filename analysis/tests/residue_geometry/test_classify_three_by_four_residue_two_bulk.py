from __future__ import annotations

import json

import unittest

from analysis.residue_geometry.classify_three_by_four_residue_two_bulk import (
    boundary_maximum,
    build_report,
    forced_forest,
    materialize,
    quotient_cycle_data,
)
from analysis._paths import analysis_path
from analysis.tests._support import migrated_artifact


ARTIFACT = analysis_path("three_by_four_residue_two_bulk.json")


class ThreeByFourResidueTwoBulkTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.report = build_report()

    def test_complete_mask_classification(self) -> None:
        scope = self.report["scope"]
        bulk = self.report["bulk_classification"]
        self.assertEqual(scope["masks_enumerated"], 4096)
        self.assertEqual(scope["weight_four_masks"], 495)
        self.assertEqual(bulk["unit_cell_survivors"], 33)
        self.assertEqual(bulk["symbolic_forced_forest_survivors"], 3)
        self.assertEqual(bulk["symmetry_phase_orbits"], 1)
        self.assertEqual(bulk["representatives"], [15])

    def test_rank_two_independent_voltages_still_have_commutator_cycles(self) -> None:
        crossed_rail = quotient_cycle_data(277)
        self.assertEqual(crossed_rail["fundamental_cycle_rank"], 2)
        self.assertEqual(crossed_rail["fundamental_cycle_voltages"], [[0, 1], [1, 0]])
        self.assertFalse(crossed_rail["lift_is_forest"])
        self.assertEqual(crossed_rail["reason"], "commutator_in_voltage_kernel")
        self.assertFalse(forced_forest(6, 8, materialize(277, 6, 8)))

    def test_true_survivors_lift_to_forests(self) -> None:
        for survivor in self.report["bulk_classification"]["survivors"]:
            self.assertTrue(survivor["quotient"]["lift_is_forest"])
            for repetitions in (2, 3, 5, 8, 13):
                self.assertTrue(forced_forest(
                    3 * repetitions,
                    4 * repetitions,
                    materialize(survivor["mask"], 3 * repetitions, 4 * repetitions),
                ))

    def test_boundary_formula_and_k_mod_four(self) -> None:
        self.assertEqual([boundary_maximum(7, phase) for phase in range(3)], [37, 30, 37])
        self.assertEqual(set(self.report["k_mod_4"]), {"0", "1", "2", "3"})
        self.assertTrue(all(
            value["maximum_total"] == "3k^2+5k+2"
            for value in self.report["k_mod_4"].values()
        ))
        self.assertEqual(self.report["target_obstruction"]["exact_deficit"], "2k-2")

    def test_k_7_8_9_maxima(self) -> None:
        expected = {7: 184, 8: 234, 9: 290}
        for record in self.report["validation"]:
            best = max(phase["total"] for phase in record["phases"])
            self.assertEqual(best, expected[record["k"]])
            self.assertTrue(all(phase["forced_forest"] for phase in record["phases"]))

    def test_artifact_is_current(self) -> None:
        self.assertEqual(migrated_artifact(json.loads(ARTIFACT.read_text())), self.report)


if __name__ == "__main__":
    unittest.main()
