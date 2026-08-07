from __future__ import annotations

import unittest

from residue_two_revised_recurrence import (
    affine_candidate,
    affine_step,
    metrics,
    revised_target,
    target_charge_candidate,
    target_charge_step,
)


class RevisedResidueTwoRecurrenceTests(unittest.TestCase):
    def test_target_charge_probe_has_exact_symbolic_increment(self) -> None:
        rows = target_charge_candidate(6)
        for k in range(6, 31):
            self.assertEqual(len(rows), 3 * k + 2)
            self.assertEqual(sum(row.count("U") for row in rows), revised_target(k))
            following = target_charge_step(rows)
            self.assertEqual(
                sum(row.count("U") for row in following) - sum(row.count("U") for row in rows),
                12 * k + 11,
            )
            rows = following

    def test_target_charge_probe_exposes_attachment_failure(self) -> None:
        source = metrics(target_charge_candidate(6))
        first = metrics(target_charge_candidate(7))
        self.assertTrue(source["dual_connected"])
        self.assertEqual((first["u"], first["dual_total"]), (333, 485))
        self.assertFalse(first["dual_connected"])

    def test_affine_recurrence_is_connected_and_forest_completable(self) -> None:
        rows = affine_candidate(5)
        for k in range(5, 41):
            self.assertEqual(rows, affine_candidate(k))
            self.assertEqual(sum(row.count("U") for row in rows), 6 * k * k + 6 * k - 1)
            result = metrics(rows)
            self.assertTrue(result["dual_connected"], k)
            self.assertTrue(result["forest_completable"], k)
            following = affine_step(rows)
            self.assertEqual(
                sum(row.count("U") for row in following) - sum(row.count("U") for row in rows),
                12 * k + 12,
            )
            rows = following


if __name__ == "__main__":
    unittest.main()
