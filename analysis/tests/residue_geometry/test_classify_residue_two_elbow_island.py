from __future__ import annotations

import json
import unittest

from analysis.residue_geometry.classify_residue_two_elbow_island import (
    DEFAULT_OUTPUT,
    build_report,
    boundary_domain_arcs,
    local_paths,
    materialize,
    transition_valid,
    unit_cells_valid,
    wall_packet_cycles,
)
from analysis.residue_geometry.classify_residue_two_staircase_seam import forced_forest
from analysis.tests._support import migrated_artifact


class ResidueTwoElbowIslandTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.report = build_report()

    def test_two_wall_cycle_grammar_is_finite(self) -> None:
        self.assertEqual(len(wall_packet_cycles()), 56)
        path = local_paths()[0]
        for row in range(3):
            self.assertTrue(transition_valid(
                row,
                path["start"] + sum(path["lower_packet"][:row]),
                path["width_cycle"][row],
                path["lower_packet"][row],
                path["upper_packet"][row],
                path["row_phase"],
                path["column_phase"],
                path["island_phase"],
                path["orientation"],
            ))

    def test_exported_best_geometry_at_k_7_8_9(self) -> None:
        best = self.report["unconstrained_best"]
        for record in best["records"]:
            n = 3 * record["k"] + 2
            core, island, _ = materialize(record["k"], best["path"])
            self.assertTrue(island)
            self.assertTrue(unit_cells_valid(n, core))
            self.assertTrue(forced_forest(n, core))
            self.assertTrue(record["cap_forced_forest"])
            self.assertEqual(boundary_domain_arcs(record["k"], best["path"]), record["boundary_domain_arcs"])

    def test_singleton_articulation_obstruction(self) -> None:
        classification = self.report["classification"]
        self.assertEqual(self.report["status"], "minimal_elbow_island_obstructed")
        self.assertEqual(classification["minimum_island_exterior_support_intersection"], 4)
        self.assertEqual(classification["singleton_articulation_paths"], 0)
        self.assertEqual(classification["stable_three_cap_arc_paths"], 56)
        self.assertEqual(classification["three_arc_singleton_paths"], 0)
        self.assertEqual(classification["target_paths"], 0)

    def test_capacity_does_not_supply_packet_gain(self) -> None:
        best = self.report["unconstrained_best"]
        self.assertEqual(best["formulas"]["total"], "3k^2 + 6k + 2")
        totals = [record["total"] for record in best["records"]]
        self.assertEqual(totals, [191, 242, 299])
        self.assertEqual([totals[1] - totals[0], totals[2] - totals[1]], [51, 57])
        self.assertFalse(self.report["lower_l2_assessment"]["blocked_beyond_declared_finite_grammars"])

    def test_three_arc_cap_class_is_stable_but_too_small(self) -> None:
        best = self.report["three_arc_best"]
        self.assertEqual(best["formulas"], {
            "cap": "5k + 2",
            "island": "k - 1",
            "seam": "0",
            "total": "3k^2 + 5k + 2",
        })
        self.assertEqual([record["cap_maximum"] for record in best["records"]], [37, 42, 47])
        self.assertTrue(all(record["boundary_domain_arcs"]["three_arcs"] for record in best["records"]))

    def test_artifact_is_current(self) -> None:
        self.assertEqual(migrated_artifact(json.loads(DEFAULT_OUTPUT.read_text())), self.report)


if __name__ == "__main__":
    unittest.main()
