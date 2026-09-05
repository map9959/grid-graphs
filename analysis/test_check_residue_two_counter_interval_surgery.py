from __future__ import annotations

import unittest

from check_residue_two_counter_interval_surgery import (
    COUNTER_ID,
    SCHEMA,
    analyze_surgery,
    analyze_surgery_transition,
    build_report,
)


class ResidueTwoCounterIntervalSurgeryTests(unittest.TestCase):
    def test_exact_target_count_and_subdivided_parent_edge(self) -> None:
        for k in (7, 8, 9, 12):
            with self.subTest(k=k):
                record = analyze_surgery(k)
                self.assertEqual(record["status"], "abstract_verified")
                self.assertEqual(record["count"]["total_length"], 3 * k * k + 7 * k)
                self.assertEqual(record["counter_interval"]["length"], k - 5)
                self.assertEqual(record["parent_overrides"][COUNTER_ID], record["affine_root"])
                self.assertEqual(record["parent_overrides"][record["detached_branch"]], COUNTER_ID)
                self.assertTrue(all(record["checks"].values()))

    def test_leaf_elimination_is_a_complete_postorder(self) -> None:
        record = analyze_surgery(7)
        self.assertEqual(len(record["leaf_elimination_order"]), 29)
        self.assertLessEqual(max(record["leaf_elimination_suffix_degrees"]), 1)
        self.assertEqual(record["leaf_elimination_order"][-1], record["affine_root"])

    def test_transition_has_exact_gain_and_uniform_parent_transport(self) -> None:
        for k in (7, 8, 9, 12):
            with self.subTest(k=k):
                transition = analyze_surgery_transition(k)
                self.assertEqual(transition["status"], "abstract_verified")
                self.assertEqual(transition["gain"]["total"], 6 * k + 10)
                self.assertEqual(transition["gain"]["counter_length_change"], 1)
                self.assertFalse(transition["parent_mismatches"])
                self.assertTrue(all(transition["checks"].values()))

    def test_report_does_not_claim_grid_geometry(self) -> None:
        report = build_report()
        self.assertEqual(report["schema"], SCHEMA)
        self.assertEqual(report["status"], "abstract_verified_geometry_open")
        self.assertTrue(all(
            record["geometry"]["status"] == "open_L3" for record in report["records"]
        ))


if __name__ == "__main__":
    unittest.main()
