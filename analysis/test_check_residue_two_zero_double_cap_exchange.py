from __future__ import annotations

import unittest

from check_residue_two_zero_double_cap_exchange import (
    RAW_DESCRIPTOR_BOUND,
    SCHEMA,
    analyze_k,
    build_report,
    iter_exact_descriptors,
)


class ResidueTwoZeroDoubleCapExchangeTests(unittest.TestCase):
    def test_hard_bounds_and_exact_descriptor_reduction(self) -> None:
        exact = list(iter_exact_descriptors())
        self.assertEqual(RAW_DESCRIPTOR_BOUND, 262_144)
        self.assertEqual(len(exact), 576)
        self.assertTrue(all(descriptor.packet_gain == 10 for descriptor in exact))
        self.assertTrue(all(descriptor.cap_gain == 16 for descriptor in exact))

    def test_complete_k7_k8_k9_obstruction(self) -> None:
        for k in (7, 8, 9):
            with self.subTest(k=k):
                record = analyze_k(k)
                self.assertEqual(record["status"], "complete_grammar_obstruction")
                self.assertTrue(all(record["checks"].values()))
                self.assertEqual(record["enumeration"]["exact_descriptors"], 576)
                self.assertEqual(record["enumeration"]["locally_valid_descriptors"], 576)
                self.assertEqual(record["obstruction"]["minimum_star_intersection"], 2)
                self.assertEqual(record["obstruction"]["minimum_forced_cycle_rank"], 4 * k - 8)
                self.assertEqual(record["obstruction"]["survivors"], 0)

    def test_best_local_materialization_has_exact_count_but_global_failure(self) -> None:
        for k in (7, 8, 9):
            best = analyze_k(k)["best_local_materialization"]
            self.assertEqual(best["replacement_count"], 10 * k - 4)
            self.assertEqual(best["forced_count"], 3 * k * k + 7 * k)
            self.assertTrue(best["checks"]["unit_cells_valid"])
            self.assertTrue(best["checks"]["components_straight"])
            self.assertFalse(best["checks"]["singleton_star_intersections"])
            self.assertFalse(best["checks"]["incidence_tree"])
            self.assertFalse(best["checks"]["forced_forest"])

    def test_report_names_sparse_rail_next_topology(self) -> None:
        report = build_report()
        self.assertEqual(report["schema"], SCHEMA)
        self.assertEqual(report["status"], "complete_grammar_obstruction")
        self.assertEqual(report["next_topology"]["packet_capacity"], 12)
        self.assertEqual(report["next_topology"]["packet_gain"], 10)


if __name__ == "__main__":
    unittest.main()
