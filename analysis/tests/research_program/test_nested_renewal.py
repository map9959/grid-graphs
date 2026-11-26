"""Lightweight cycle3 checks; no pair search, diagnostic run, or artifact writes."""

import unittest

from analysis.research_program.nested_renewal import (
    compose, depth, direct_q, enumerate_supersets, geometry_report,
    ledger, pair_report, recorded_report, singleton_report, source_i, traverse,
)
from analysis.research_program.renewal_annulus import audit


class NestedRenewalTests(unittest.TestCase):
    def test_direct_geometry_and_old_deep_u_exclusion(self):
        for n, counts in ((8, (23, 1, 22)), (14, (69, 23, 46))):
            report = geometry_report(n)
            self.assertEqual(tuple(report["observed_counts"].values()), counts)
            q = direct_q(n)
            deep = {v for v in range(n*n) if depth(n, v) >= 3}
            self.assertEqual(q & deep, source_i(n) & deep)
            self.assertFalse(set(report["allowed_hole_ids"]) & deep)
            self.assertEqual(report["q"]["ledger"], audit(n, sorted(q)))
        small = geometry_report(8)
        self.assertEqual(len(small["allowed_hole_ids"]), 38)
        self.assertEqual(len(small["immutable_deep_u_ids"]), 3)
        self.assertEqual(small["q"]["rows"], [
            "UFUUFUUF", "UUUUFUUF", "FUFUFUUF", "FUUUFUUF",
            "FUUUUUUF", "FUUFUFUF", "FUUFUUUF", "FUUFUUUU",
        ])

    def test_size_guards_prevent_n20(self):
        for n in (2, 11, 15, 20, True, 8.0):
            for function in (direct_q, source_i, geometry_report):
                with self.assertRaises(ValueError):
                    function(n)
            with self.assertRaises(ValueError):
                ledger(n, [])

    def test_traversal_detects_nonlocal_cycle_and_isolates(self):
        # Exercise a long cycle directly: traversal must not be square-only.
        cycle = [[(v-1) % 8, (v+1) % 8] for v in range(8)] + [[]]
        self.assertEqual(traverse(cycle, range(9)), (2, False))
        cycle[0].remove(7)
        cycle[7].remove(0)
        self.assertEqual(traverse(cycle, range(9)), (2, True))
        opposite = {3*8+3, 4*8+4}
        for n, centers in ((8, set()), (8, {3*8+4}), (8, opposite),
                           (8, direct_q(8)), (14, direct_q(14))):
            self.assertEqual(ledger(n, centers), audit(n, sorted(centers)))
        self.assertFalse(ledger(8, opposite)["forest"])
        self.assertEqual(ledger(8, set())["c"], 64)
        with self.assertRaises(ValueError):
            ledger(8, [1, 1])

    def test_empty_and_one_bit_pool_masks(self):
        result = enumerate_supersets(8, direct_q(8), [])
        self.assertTrue(result["exhaustive"])
        self.assertEqual(result["tested_supermasks"], 1)
        self.assertEqual(result["feasible_masks"], [0])
        self.assertEqual(result["maximum_f"], 23)
        singles = singleton_report(8, set(), [0])
        self.assertEqual(singles["eligible_ids"], [0])
        result = enumerate_supersets(8, set(), [0])
        self.assertEqual(result["feasible_masks"], [0, 1])
        self.assertEqual(result["best_masks"], [1])
        self.assertEqual(result["best_boards"][0]["center_ids"], [0])

    def test_cutoff_is_not_an_optimum(self):
        # Every singleton on an otherwise empty board is feasible; no masks
        # are enumerated when the pool exceeds the fixed cap.
        result = enumerate_supersets(8, set(), list(range(21)))
        self.assertEqual(result["status"], "cutoff_inconclusive")
        self.assertFalse(result["exhaustive"])
        self.assertIsNone(result["maximum_f"])
        self.assertEqual(result["tested_supermasks"], 0)
        self.assertEqual(result["feasible_masks"], [])

    def test_pair_and_composition_reject_old_deep_u(self):
        report = geometry_report(8)
        holes = report["allowed_hole_ids"].copy()
        deep_u = report["immutable_deep_u_ids"][0]
        holes[0] = deep_u
        with self.assertRaises(ValueError):
            pair_report(direct_q(8), holes)
        with self.assertRaises(ValueError):
            compose([deep_u, report["allowed_hole_ids"][0]], set())

    def test_recorded_rewrites_and_crop(self):
        small = recorded_report(8)
        large = recorded_report(14)
        self.assertEqual((small["delete_count"], small["add_count"]), (10, 7))
        self.assertTrue(small["all_changes_in_old_band"])
        self.assertTrue(large["all_changes_in_old_band"])
        self.assertEqual(large["net_deleted"], 6)
        crop = {v for v in large["board"]["center_ids"] if depth(14, v) >= 3}
        self.assertEqual(crop, {(v//8+3)*14+v % 8+3 for v in direct_q(8)})


if __name__ == "__main__":
    unittest.main()
