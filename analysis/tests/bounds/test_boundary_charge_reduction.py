from __future__ import annotations

import unittest

from analysis.bounds.boundary_charge_reduction import (
    boundary_charges,
    exhaustive_sets,
    maximum_forced_plus_isolated,
)
from analysis.bounds.forced_forest_row_grammar import maximum_forced_forest


class BoundaryChargeReductionTests(unittest.TestCase):
    def test_identity_on_every_acyclic_set_through_n3(self) -> None:
        for n in range(1, 4):
            for rows in exhaustive_sets(n):
                item = boundary_charges(n, rows)
                self.assertEqual(
                    3 * item.forced_count,
                    n * n + item.charged_expression,
                )

    def test_exhaustive_maxima_agree_with_row_grammar_through_n4(self) -> None:
        for n in range(1, 5):
            observed = max(boundary_charges(n, rows).forced_count for rows in exhaustive_sets(n))
            self.assertEqual(observed, maximum_forced_forest(n))

    def test_augmented_grammar_agrees_with_brute_force_through_n3(self) -> None:
        for n in range(1, 4):
            expected = max(
                3 * item.forced_count + item.isolated_u
                for item in (boundary_charges(n, rows) for rows in exhaustive_sets(n))
            )
            observed, _peak, _rows = maximum_forced_plus_isolated(n)
            self.assertEqual(observed, expected)


if __name__ == "__main__":
    unittest.main()
