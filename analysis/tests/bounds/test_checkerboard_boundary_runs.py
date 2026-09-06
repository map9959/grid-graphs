from __future__ import annotations

import unittest

from analysis.bounds.checkerboard_boundary_runs import (
    acyclic_row_sets,
    allowances,
    boundary_vertices,
    labels_nonalternating,
    profile,
    run_bound_margins,
)
from analysis.bounds.forced_forest_row_grammar import is_forced_forest


class CheckerboardBoundaryRunTests(unittest.TestCase):
    def test_boundary_cycle_has_each_boundary_vertex_once(self) -> None:
        for n in range(2, 8):
            boundary = boundary_vertices(n)
            self.assertEqual(len(boundary), 4 * n - 4)
            self.assertEqual(len(set(boundary)), len(boundary))

    def test_charge_matches_color_cardinality_form(self) -> None:
        item = profile(5, (17, 17, 21, 1, 25))
        self.assertEqual(item.black.charge, 3 * item.black.forced - 12 + 2)
        self.assertEqual(item.white.charge, 3 * item.white.forced - 13 + 2)
        self.assertEqual(item.black.label_runs, 4)
        self.assertEqual(item.white.label_runs, 8)

    def test_candidate_on_every_acyclic_set_through_four(self) -> None:
        for n in range(2, 5):
            for rows in acyclic_row_sets(n):
                item = profile(n, rows)
                self.assertGreaterEqual(
                    min(run_bound_margins(item)), 0, (n, rows)
                )
                self.assertTrue(labels_nonalternating(item.black.labels))
                self.assertTrue(labels_nonalternating(item.white.labels))

    def test_summing_color_inequalities_is_checkerboard_bound(self) -> None:
        item = profile(4, (9, 9, 0, 15))
        black_allowance, white_allowance = allowances(4)
        self.assertEqual(black_allowance + white_allowance, 12)
        self.assertEqual(item.black.charge + item.white.charge, 12)
        self.assertEqual(run_bound_margins(item), (0, 0))

    def test_pair_is_not_an_algebraic_restatement_of_its_sum(self) -> None:
        # This cyclic forced graph meets the summed bound but fails the white
        # inequality. Acyclicity is substantive in the candidate pair.
        item = profile(4, (13, 13, 9, 1))
        self.assertEqual(item.black.charge + item.white.charge, 12)
        self.assertEqual(run_bound_margins(item), (2, -2))

    def test_nearby_coefficients_have_small_counterexamples(self) -> None:
        # The 5x5 witness forces coefficient >= 1/2 for odd bias three.
        lower = profile(5, (17, 17, 21, 1, 25))
        self.assertLess(
            min(run_bound_margins(lower, scale=3, run_coefficient=1)), 0
        )
        # The 6x6 witness forces coefficient <= 1/2.
        upper = profile(6, (37, 33, 41, 33, 0, 63))
        self.assertLess(
            min(run_bound_margins(upper, scale=3, run_coefficient=2)), 0
        )

    def test_candidate_has_forced_acyclic_7x7_counterexample(self) -> None:
        rows = (79, 64, 84, 65, 17, 1, 125)
        self.assertTrue(is_forced_forest(7, list(rows)))
        item = profile(7, rows)
        self.assertEqual(
            (
                item.black.forced,
                item.white.forced,
                item.black.label_runs,
                item.white.label_runs,
                item.black.charge,
                item.white.charge,
            ),
            (12, 8, 6, 8, 14, 1),
        )
        self.assertEqual(run_bound_margins(item), (-2, 14))

    def test_opposite_color_has_forced_acyclic_9x9_counterexample(self) -> None:
        rows = (509, 1, 137, 1, 297, 257, 257, 341, 273)
        self.assertTrue(is_forced_forest(9, list(rows)))
        item = profile(9, rows)
        self.assertEqual(
            (
                item.black.forced,
                item.white.forced,
                item.black.label_runs,
                item.white.label_runs,
                item.black.charge,
                item.white.charge,
            ),
            (13, 16, 6, 14, 1, 9),
        )
        self.assertEqual(run_bound_margins(item), (36, -2))

    def test_one_center_run_and_margin_delta_on_counterexample(self) -> None:
        rows = (79, 64, 84, 65, 17, 1, 125)
        item = profile(7, rows)
        current_margins = run_bound_margins(item)
        for row in range(7):
            for column in range(7):
                if not rows[row] >> column & 1:
                    continue
                removed_rows = list(rows)
                removed_rows[row] &= ~(1 << column)
                removed = profile(7, removed_rows)
                removed_margins = run_bound_margins(removed)
                if (row + column) % 2 == 0:
                    charge = removed.black.label_runs - item.black.label_runs
                    self.assertEqual(
                        removed.white.label_runs, item.white.label_runs
                    )
                    self.assertEqual(
                        current_margins,
                        (
                            removed_margins[0] - (6 - charge),
                            removed_margins[1] - charge,
                        ),
                    )
                else:
                    charge = removed.white.label_runs - item.white.label_runs
                    self.assertEqual(
                        removed.black.label_runs, item.black.label_runs
                    )
                    self.assertEqual(
                        current_margins,
                        (
                            removed_margins[0] - charge,
                            removed_margins[1] - (6 - charge),
                        ),
                    )


if __name__ == "__main__":
    unittest.main()
