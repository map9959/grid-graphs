from __future__ import annotations

import unittest

from analysis.bounds.bundle_cycle_defect_census import maximal_profiles
from analysis.bounds.insertion_circuit_congestion import select_insertion_circuits
from analysis.bounds.minimum_reflex_gate import (
    KNOWN_COUNTEREXAMPLE,
    minimum_reflex_profile,
    owner_minimum_reflex_counts,
    summarize,
)


class MinimumReflexGateTests(unittest.TestCase):
    def test_owner_minima_equal_independent_minimum_turn_selection(self) -> None:
        for n in range(2, 5):
            for rows, _base in maximal_profiles(n):
                minima = owner_minimum_reflex_counts(n, rows)
                selected = select_insertion_circuits(n, rows, "minimum_turns")
                self.assertEqual(
                    minima,
                    tuple((circuit.turns - 4) // 2 for circuit in selected),
                )

    def test_exact_objective_census_through_five(self) -> None:
        expected = {
            2: (4, 0, 4, 0),
            3: (26, -2, 0, 0),
            4: (138, 0, 14, 0),
            5: (2164, -3, 0, 0),
        }
        for n, wanted in expected.items():
            samples = [
                (rows, minimum_reflex_profile(n, rows))
                for rows, _base in maximal_profiles(n)
            ]
            observed = (
                len(samples),
                max(profile.objective for _rows, profile in samples),
                sum(profile.equality for _rows, profile in samples),
                sum(
                    profile.equality and profile.minimum_reflex > 0
                    for _rows, profile in samples
                ),
            )
            self.assertEqual(observed, wanted)

    def test_summary_retains_positive_reflex_witness_separately(self) -> None:
        rows = (4, 5, 17, 0, 31)
        profile = minimum_reflex_profile(5, rows)
        self.assertGreater(profile.minimum_reflex, 0)
        summary = summarize(5, "regression", [(rows, profile)])
        self.assertEqual(summary["maximum_objective"], -4)
        self.assertIsNotNone(summary["first_maximum_positive_reflex_witness"])

    def test_nine_by_nine_counterexample_replays_full_enumerator(self) -> None:
        rows = KNOWN_COUNTEREXAMPLE
        profile = minimum_reflex_profile(9, rows)
        self.assertEqual(
            (
                profile.forced,
                profile.unforced_components,
                profile.minimum_reflex,
                profile.positive_reflex_owners,
                profile.maximum_owner_minimum,
                profile.target_slack_before_reflex,
                profile.objective,
            ),
            (33, 1, 4, 3, 2, 5, 3),
        )
        selected = select_insertion_circuits(9, rows, "minimum_turns")
        self.assertEqual(sum((circuit.turns - 4) // 2 for circuit in selected), 4)


if __name__ == "__main__":
    unittest.main()
