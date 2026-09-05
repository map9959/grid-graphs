from __future__ import annotations

import unittest

from checkerboard_boundary_runs import acyclic_row_sets
from forced_forest_row_grammar import is_forced_forest
from gap_inequality_falsification import (
    component_gap_count,
    exact_maximum_score,
    line_gap_count,
    local_gap_count,
    margin,
    maximal_sets,
    score,
)
from straight_carrier_inequality import is_inclusion_maximal


class GapInequalityFalsificationTests(unittest.TestCase):
    def test_line_definition_does_not_skip_singletons(self) -> None:
        self.assertEqual(line_gap_count(map(int, "110011")), 1)
        self.assertEqual(line_gap_count(map(int, "1101011")), 0)
        self.assertEqual(line_gap_count(map(int, "1100110011")), 2)

    def test_local_definition_matches_component_definition_through_four(self) -> None:
        for n in range(2, 5):
            for rows in acyclic_row_sets(n):
                self.assertEqual(local_gap_count(n, rows), component_gap_count(n, rows), (n, rows))

    def test_weighted_grammar_matches_direct_exhaustion_through_four(self) -> None:
        for n in range(2, 5):
            direct = max((score(n, rows), rows) for rows in acyclic_row_sets(n))
            exact = exact_maximum_score(n)
            self.assertEqual(exact.maximum, direct[0])
            self.assertEqual(exact.margin, margin(n, exact.rows))

    def test_maximal_enumerator_is_complete_at_three(self) -> None:
        rows = list(maximal_sets(3))
        self.assertEqual(len(rows), 26)
        self.assertGreaterEqual(min(margin(3, item) for item in rows), 0)

    def test_n10_counterexample_independent_replay(self) -> None:
        rows = (957, 1, 585, 585, 585, 585, 585, 585, 512, 631)
        self.assertTrue(is_forced_forest(10, list(rows)))
        self.assertTrue(is_inclusion_maximal(10, rows))
        self.assertEqual(local_gap_count(10, rows), 2)
        self.assertEqual(component_gap_count(10, rows), 2)
        self.assertEqual(score(10, rows), 127)
        self.assertEqual(margin(10, rows), -1)


if __name__ == "__main__":
    unittest.main()
