from __future__ import annotations

import unittest

from analysis.bounds.straight_carrier_inequality import (
    carrier_profile,
    search_strengthenings,
)
from analysis.bounds.checkerboard_boundary_runs import acyclic_row_sets


class StraightCarrierInequalityTests(unittest.TestCase):
    def test_horizontal_carrier_statistics(self) -> None:
        item = carrier_profile(4, (15, 0, 0, 0))
        self.assertEqual(item.singleton_components, 0)
        self.assertEqual(item.horizontal_carriers, 1)
        self.assertEqual(item.vertical_carriers, 0)
        carrier = item.carriers[0]
        self.assertEqual(
            (
                carrier.length,
                carrier.side_contacts,
                carrier.attachment_degree,
                carrier.rows_occupied,
                carrier.columns_occupied,
            ),
            (4, 6, 4, 1, 4),
        )

    def test_collinear_internal_and_boundary_u_gaps(self) -> None:
        item = carrier_profile(5, (3, 0, 0, 0, 24))
        self.assertEqual(item.horizontal_carriers, 2)
        self.assertEqual(item.internal_u_gaps, 0)
        self.assertEqual(item.boundary_u_gaps, 2)
        self.assertEqual(item.boundary_u_gap_vertices, 6)

    def test_nonnegative_search_is_a_genuine_strengthening(self) -> None:
        profiles = [carrier_profile(4, rows) for rows in ((9, 9, 0, 15), (0, 0, 0, 0))]
        for coefficients in search_strengthenings(profiles):
            self.assertTrue(any(coefficients))
            self.assertTrue(all(coefficient >= 0 for coefficient in coefficients))

    def test_candidate_on_every_acyclic_set_through_four(self) -> None:
        for n in range(2, 5):
            for rows in acyclic_row_sets(n):
                item = carrier_profile(n, rows)
                self.assertGreaterEqual(
                    item.target_margin - 2 * item.internal_u_gaps,
                    0,
                    (n, rows),
                )

    def test_n12_pins_gap_count_coefficient_and_rejects_length(self) -> None:
        rows = (4093, 1, 513, 2301, 2049, 2817, 2169, 2049, 2957, 2081, 1, 4093)
        item = carrier_profile(12, rows)
        self.assertEqual(
            (item.target_margin, item.internal_u_gaps, item.internal_u_gap_vertices),
            (2, 1, 3),
        )
        self.assertEqual(item.target_margin - 2 * item.internal_u_gaps, 0)
        self.assertLess(item.target_margin - 3 * item.internal_u_gaps, 0)
        self.assertLess(item.target_margin - item.internal_u_gap_vertices, 0)

    def test_branching_attachments_do_not_supply_extra_credit(self) -> None:
        item = carrier_profile(4, (1, 9, 8, 11))
        self.assertEqual(item.target_margin, 3)
        self.assertEqual(item.carrier_branching_attachments, 4)

    def test_gap_term_is_not_algebraically_zero(self) -> None:
        item = carrier_profile(5, (0, 0, 0, 0, 27))
        self.assertEqual(item.internal_u_gaps, 1)
        self.assertEqual(item.internal_u_gap_vertices, 1)


if __name__ == "__main__":
    unittest.main()
