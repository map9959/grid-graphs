from __future__ import annotations

import unittest

from analysis.bounds.forced_forest_row_grammar import is_forced_forest, maximum_forced_forest


def direct_maximum(n: int) -> int:
    """Enumerate all F subsets, independently of frontier-state compression."""
    best = 0
    row_mask = (1 << n) - 1
    for forced_set in range(1 << (n * n)):
        rows = [(forced_set >> (row * n)) & row_mask for row in range(n)]
        if forced_set.bit_count() > best and is_forced_forest(n, rows):
            best = forced_set.bit_count()
    return best


class ForcedForestRowGrammarTests(unittest.TestCase):
    def test_exactly_matches_direct_enumeration_through_four(self) -> None:
        for n in range(1, 5):
            with self.subTest(n=n):
                self.assertEqual(maximum_forced_forest(n), direct_maximum(n))

    def test_matches_existing_exact_diagonal_values(self) -> None:
        # data/diagonal.csv: P(n,n), equal to max forced-acyclic by forest extension.
        expected = [1, 2, 4, 8, 11, 16]
        self.assertEqual([maximum_forced_forest(n) for n in range(1, 7)], expected)

    def test_reconstructed_optimum_is_a_forced_forest(self) -> None:
        maximum, rows = maximum_forced_forest(5, witness=True)
        self.assertEqual(maximum, 11)
        self.assertEqual(sum(mask.bit_count() for mask in rows), maximum)
        self.assertTrue(is_forced_forest(5, rows))


if __name__ == "__main__":
    unittest.main()
