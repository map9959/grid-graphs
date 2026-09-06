from __future__ import annotations

import json
import unittest

from analysis._paths import analysis_path
from analysis.residue_geometry.classify_six_by_six_residue_two_bulk import (
    adjacent_rows_valid,
    boundary_grammar,
    build_report,
    cyclic_row_walks,
    gap_grammar_maximum,
    quotient_cycle_data,
    row_transition_table,
)
from analysis.tests._support import migrated_artifact

ARTIFACT = analysis_path("six_by_six_residue_two_bulk.json")


class SixBySixResidueTwoBulkTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.report = build_report()

    def test_row_automaton_is_complete_without_mask_enumeration(self) -> None:
        automaton = self.report["row_automaton"]
        self.assertEqual(automaton["states"], 64)
        self.assertEqual(automaton["directed_transitions"], 324)
        self.assertEqual(automaton["closed_weight_twelve_walks"], 110832)
        self.assertEqual(len(cyclic_row_walks()), 110832)
        transitions = row_transition_table()
        self.assertTrue(all(adjacent_rows_valid(left, right) for left, targets in enumerate(transitions) for right in targets))

    def test_symbolic_quotient_and_symmetry_classification(self) -> None:
        bulk = self.report["bulk_classification"]
        self.assertEqual(bulk["symbolic_forced_forest_survivors"], 6)
        self.assertEqual(bulk["torus_dihedral_orbits"], 1)
        self.assertEqual(bulk["representative_row_masks"], [0, 0, 63, 0, 0, 63])
        for survivor in bulk["survivors"]:
            quotient = quotient_cycle_data(tuple(survivor["row_masks"]))
            self.assertTrue(quotient["lift_is_forest"])
            self.assertEqual([component["fundamental_rank"] for component in quotient["components"]], [1, 1])
            self.assertTrue(survivor["open_boxes_2_through_8"])

    def test_nonabelian_criterion_rejects_higher_rank_components(self) -> None:
        rejected = self.report["bulk_classification"]["quotient_rejections_by_bad_component_ranks"]
        self.assertGreater(rejected["3"], 0)
        self.assertTrue(all(
            int(rank) >= 2
            for ranks in rejected
            for rank in ranks.split(",")
        ))
        self.assertEqual(
            sum(rejected.values()) + self.report["bulk_classification"]["symbolic_forced_forest_survivors"],
            110832,
        )

    def test_finite_boundary_grammar(self) -> None:
        self.assertEqual([boundary_grammar(7, phase)["maximum"] for phase in range(3)], [37, 30, 37])
        self.assertEqual([gap_grammar_maximum(3 * k + 2) for k in (7, 8, 9)], [8, 9, 10])
        self.assertEqual(self.report["boundary_grammar"]["maximum_total"], "3k^2+5k+2")
        self.assertFalse(self.report["target_decision"]["attainable_for_all_k_at_least_7"])

    def test_k_7_8_9_formula_validation(self) -> None:
        expected = {7: (184, 196), 8: (234, 248), 9: (290, 306)}
        for record in self.report["validation"]:
            maximum = max(phase["total"] for phase in record["phases"])
            self.assertEqual((maximum, record["target"]), expected[record["k"]])
            self.assertTrue(all(phase["forced_forest"] for phase in record["phases"]))

    def test_artifact_is_current(self) -> None:
        self.assertEqual(migrated_artifact(json.loads(ARTIFACT.read_text())), self.report)


if __name__ == "__main__":
    unittest.main()
