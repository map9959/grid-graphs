from __future__ import annotations

import unittest

from analysis.residue_geometry.check_residue_two_zero_two_layer_ladder import (
    SCHEMA,
    analyze_k,
    build_report,
    iter_descriptors,
)


class ResidueTwoZeroTwoLayerLadderTests(unittest.TestCase):
    def test_declared_grammar_has_hard_bounds(self) -> None:
        descriptors = list(iter_descriptors())
        exact = [descriptor for descriptor in descriptors if descriptor.packet_gain == 7]
        self.assertEqual(len(descriptors), 4096)
        self.assertEqual(len(exact), 48)
        self.assertTrue(all(
            descriptor.bottom_mask == descriptor.right_mask == 7
            and descriptor.rung_offset is not None
            for descriptor in exact
        ))

    def test_k7_k8_k9_are_complete_obstructions(self) -> None:
        for k in (7, 8, 9):
            with self.subTest(k=k):
                record = analyze_k(k)
                self.assertEqual(record["status"], "complete_grammar_obstruction")
                self.assertTrue(all(record["checks"].values()))
                self.assertEqual(record["enumeration"]["materializations_checked"], 48)
                self.assertEqual(record["obstruction"]["survivors"], 0)
                self.assertEqual(
                    record["obstruction"]["parallel_right_rail_intersection"],
                    3 * k - 5,
                )
                self.assertEqual(record["obstruction"]["minimum_forced_cycle_rank"], 3 * k - 5)

    def test_best_exact_materializations_pass_local_but_not_global_checks(self) -> None:
        for k in (7, 8, 9):
            checks = analyze_k(k)["best_exact_materialization"]["checks"]
            self.assertTrue(checks["exact_target_count"])
            self.assertTrue(checks["unit_cells_valid"])
            self.assertTrue(checks["components_straight"])
            self.assertTrue(checks["stable_packet_gain_seven"])
            self.assertFalse(checks["singleton_star_intersections"])
            self.assertFalse(checks["tree_incidence"])
            self.assertFalse(checks["forced_forest"])

    def test_report_names_exact_next_topology(self) -> None:
        report = build_report()
        self.assertEqual(report["schema"], SCHEMA)
        self.assertEqual(report["status"], "complete_grammar_obstruction")
        self.assertEqual(report["next_topology"]["replacement_count"], "10k-4")
        self.assertEqual(report["next_topology"]["successor_packet_gain"], 10)


if __name__ == "__main__":
    unittest.main()
