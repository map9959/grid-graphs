from __future__ import annotations

import unittest

from analysis._paths import analysis_path
from analysis.patterns.construction_lab import (
    dual_connectivity_check,
    forest_completion_check,
    run_check,
)
from analysis.patterns.diagonal_patterns import (
    q_formula,
    q_old_formula,
    residue_two_affine_pattern,
    residue_two_pattern,
    residue_two_revised_pattern,
)


class DiagonalPatternTests(unittest.TestCase):
    def test_revised_residue_two_formula_boundary(self) -> None:
        self.assertEqual(q_formula(14), 119)
        self.assertEqual(q_old_formula(17), 178)
        self.assertEqual(q_formula(17), 179)
        self.assertEqual(q_old_formula(20), 249)
        self.assertEqual(q_formula(20), 250)
        self.assertEqual(q_formula(23), 333)

    def test_canonical_revised_bases_replay(self) -> None:
        for n in (17, 20):
            rows = residue_two_pattern(n)
            self.assertEqual(rows, residue_two_revised_pattern(n))
            self.assertTrue(run_check(n, rows)["all_ok"])
            self.assertTrue(dual_connectivity_check(rows)[0])
            self.assertTrue(forest_completion_check(rows)[0])
        cached_17 = analysis_path("residue_two_affine_17_witness.txt").read_text().splitlines()
        cached_17 = [row for row in cached_17 if row and not row.startswith("#")]
        self.assertEqual(residue_two_pattern(17), cached_17)

    def test_affine_family_is_not_canonical_after_n17(self) -> None:
        self.assertEqual(residue_two_pattern(17), residue_two_affine_pattern(17))
        self.assertEqual(sum(row.count("U") for row in residue_two_affine_pattern(20)), 251)
        self.assertEqual(sum(row.count("U") for row in residue_two_pattern(20)), 250)
        with self.assertRaises(KeyError):
            residue_two_pattern(23)


if __name__ == "__main__":
    unittest.main()
