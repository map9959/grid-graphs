from __future__ import annotations

import unittest

from analysis.bounds.forced_forest_diagonal_cegar import (
    enumerate_complete_source,
    feature,
    solve_constraints,
)
from analysis.bounds.forced_forest_row_grammar import State


class ForcedForestDiagonalCegarTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.sources = [enumerate_complete_source(n) for n in range(3, 8)]

    def test_complete_source_census_and_charge(self) -> None:
        source = self.sources[0]
        self.assertEqual([len(layer) for layer in source.layers], [1, 8, 14, 14])
        self.assertEqual([len(edges) for edges in source.edges], [8, 24, 52])
        self.assertEqual(source.optimum, 6)
        self.assertEqual((3 * 3 + 3 * 3 - source.optimum) // 3, 4)

    def test_one_block_debt_fails_on_held_out_equality_corridor(self) -> None:
        discovery = solve_constraints(
            self.sources[:4], "ownership+top-debt", 0, "universal"
        )
        held_out = solve_constraints(
            self.sources, "ownership+top-debt", 0, "universal"
        )
        self.assertTrue(discovery["feasible"])
        self.assertEqual(discovery["potential_denominators"], [1])
        self.assertFalse(held_out["feasible"])
        self.assertEqual(held_out["negative_cycle_weight"], -4)

    def test_saturated_component_reserve_survives_complete_held_out_source(self) -> None:
        universal = solve_constraints(
            self.sources, "components+reserve", None, "universal"
        )
        residue_zero = solve_constraints(
            self.sources, "components+reserve", None, "residue-zero"
        )
        self.assertTrue(universal["feasible"])
        self.assertTrue(residue_zero["feasible"])
        self.assertEqual(residue_zero["potential_denominators"], [1])
        self.assertGreaterEqual(residue_zero["terminal_minima"]["3"], 4)
        self.assertGreaterEqual(residue_zero["terminal_minima"]["6"], 4)

    def test_reserve_saturates_after_six_rows(self) -> None:
        state = State(0, tuple(range(10)))
        self.assertEqual(feature(10, 5, state, "components+reserve")[-1], 5)
        self.assertEqual(feature(10, 6, state, "components+reserve")[-1], 6)
        self.assertEqual(feature(10, 9, state, "components+reserve")[-1], 6)


if __name__ == "__main__":
    unittest.main()
