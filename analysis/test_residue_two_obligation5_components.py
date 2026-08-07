#!/usr/bin/env python3

import unittest

from diagonal_patterns import residue_two_affine_pattern, residue_two_explicit_pattern
from residue_two_obligation5_components import check_component_reduction


class Obligation5ComponentReductionTests(unittest.TestCase):
    def test_known_curvature_five_controls_are_sharp(self) -> None:
        expected = {
            5: (7, 4, 1),
            8: (6, 8, 1),
            11: (5, 11, 2),
            14: (5, 14, 2),
        }
        for n, terms in expected.items():
            with self.subTest(n=n):
                result = check_component_reduction(residue_two_explicit_pattern(n))
                self.assertEqual(
                    (result.boundary_u, result.full_components, result.forced_components),
                    terms,
                )
                self.assertEqual(result.component_charge, n + 7)
                self.assertEqual(result.curvature, 5)

    def test_all_u_pattern(self) -> None:
        result = check_component_reduction(["UUU"] * 3)
        self.assertEqual(result.full_components, 0)
        self.assertEqual(result.forced_components, 9)
        self.assertEqual(result.component_charge, 21)
        self.assertEqual(result.curvature, 16)

    def test_n17_surplus_control(self) -> None:
        result = check_component_reduction(residue_two_affine_pattern(17))
        self.assertEqual(
            (result.boundary_u, result.full_components, result.forced_components),
            (5, 20, 2),
        )
        self.assertEqual(result.component_charge, 27)
        self.assertEqual(result.curvature, 8)

    def test_rejects_forced_cycle(self) -> None:
        with self.assertRaisesRegex(ValueError, "not a forest"):
            check_component_reduction(["..."] * 3)


if __name__ == "__main__":
    unittest.main()
