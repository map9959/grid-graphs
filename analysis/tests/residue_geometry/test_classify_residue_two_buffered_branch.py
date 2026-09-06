from __future__ import annotations

import json
import unittest

from analysis.residue_geometry.classify_residue_two_buffered_branch import (
    DEFAULT_OUTPUT,
    build_report,
    endpoint_states,
    local_paths,
    materialize,
    unit_cells_valid,
    wall_packets,
)
from analysis.residue_geometry.classify_residue_two_staircase_seam import forced_forest
from analysis.tests._support import migrated_artifact


class ResidueTwoBufferedBranchTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.report = build_report()

    def test_finite_grammar_sizes(self) -> None:
        self.assertEqual(len(wall_packets()), 10)
        self.assertEqual(len(endpoint_states()), 19)
        self.assertTrue(local_paths())

    def test_best_stable_singleton_geometry(self) -> None:
        best = self.report["best_singleton_path"]
        for record in best["records"]:
            n = 3 * record["k"] + 2
            core, branch, exterior = materialize(record["k"], best["path"], tuple(best["endpoint"]))
            self.assertTrue(branch and exterior)
            self.assertTrue(unit_cells_valid(n, core))
            self.assertTrue(forced_forest(n, core))
            self.assertTrue(record["articulation"]["singleton"])
            self.assertTrue(record["forced_forest"])

    def test_target_and_parent_tree_classification(self) -> None:
        classification = self.report["classification"]
        self.assertEqual(self.report["status"], "buffered_branch_obstructed")
        self.assertGreater(classification["stable_singleton_paths"], 0)
        self.assertEqual(classification["stable_parent_tree_paths"], 0)
        self.assertEqual(classification["target_paths"], 0)
        self.assertTrue(self.report["lower_gate"]["declared_finite_grammars_exhausted"])

    def test_best_formula_and_stable_gain(self) -> None:
        best = self.report["best_singleton_path"]
        self.assertEqual(best["formulas"], {
            "branch": "k",
            "bulk_correction": "-6k + 7",
            "cap": "8k + 3",
            "total": "3k^2 + 2k + 10",
        })
        totals = [record["total"] for record in best["records"]]
        self.assertEqual(totals, [171, 218, 271])
        self.assertEqual(
            self.report["obstruction"]["best_successor_gains"],
            [totals[1] - totals[0], totals[2] - totals[1]],
        )
        self.assertTrue(all(total < record["target"] for total, record in zip(totals, best["records"])))
        self.assertTrue(self.report["stable_interface"]["best_path_stable"])
        self.assertTrue(all(record["incidence"]["maximum_star_intersection"] <= 1 for record in best["records"]))

    def test_artifact_is_current(self) -> None:
        self.assertEqual(migrated_artifact(json.loads(DEFAULT_OUTPUT.read_text())), self.report)


if __name__ == "__main__":
    unittest.main()
