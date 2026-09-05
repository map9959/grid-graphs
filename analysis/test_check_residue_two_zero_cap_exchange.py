from __future__ import annotations

import unittest

from check_residue_two_zero_cap_exchange import SCHEMA, analyze_k, build_report


class ResidueTwoZeroCapExchangeTests(unittest.TestCase):
    def test_source_and_retained_interval_formulas(self) -> None:
        for k in (7, 8, 9):
            with self.subTest(k=k):
                record = analyze_k(k)
                self.assertEqual(record["status"], "obstructed")
                self.assertTrue(all(record["checks"].values()))
                self.assertEqual(record["source_interval_skeleton"]["nodes"], 3 * k - 1)
                self.assertEqual(record["source_interval_skeleton"]["links"], 3 * k - 2)
                self.assertTrue(record["source_interval_skeleton"]["tree"])
                self.assertEqual(record["retained_interval_forest"]["components"], k)

    def test_exact_replacement_count_and_complete_outer_capacity(self) -> None:
        for k in (7, 8, 9):
            with self.subTest(k=k):
                counts = analyze_k(k)["counts"]
                self.assertEqual(counts["required_replacement"], 7 * k + 1)
                self.assertEqual(counts["outer_arm_capacity"], 3 * k + 5)
                self.assertEqual(counts["fixed_hub_grammar_capacity"], 6 * k + 4)
                self.assertEqual(counts["deficit"], k - 3)

    def test_stable_interface_loses_one_per_successor(self) -> None:
        records = [analyze_k(k) for k in (7, 8, 9)]
        capacities = [record["counts"]["fixed_hub_grammar_capacity"] for record in records]
        required = [record["counts"]["required_replacement"] for record in records]
        self.assertEqual(capacities, [46, 52, 58])
        self.assertEqual(required, [50, 57, 64])
        self.assertEqual([right - left for left, right in zip(capacities, capacities[1:])], [6, 6])
        self.assertEqual([right - left for left, right in zip(required, required[1:])], [7, 7])

    def test_report_is_scoped_complete_obstruction(self) -> None:
        report = build_report()
        self.assertEqual(report["schema"], SCHEMA)
        self.assertEqual(report["status"], "complete_grammar_obstruction")
        self.assertEqual(report["k_values"], [7, 8, 9])
        self.assertEqual(report["symbolic_obstruction"]["deficit"], "k-3")


if __name__ == "__main__":
    unittest.main()
