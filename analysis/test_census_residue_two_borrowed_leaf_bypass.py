from __future__ import annotations

import unittest

from census_residue_two_borrowed_leaf_bypass import (
    SCHEMA,
    build_report,
    derive_borrowed_choices,
    replay_choice,
)


class ResidueTwoBorrowedLeafBypassTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.report = build_report()

    def test_exact_hard_caps(self) -> None:
        derivation = derive_borrowed_choices()
        self.assertEqual(len(derivation["types"]), 5)
        self.assertEqual(len(derivation["attempts"]), 20)
        self.assertEqual(self.report["grammar"]["other_edits"], "none")

    def test_every_borrowed_choice_is_classified(self) -> None:
        count = self.report["grammar"]["borrowed_choices"]
        self.assertEqual(len(self.report["chains"]), count)
        self.assertEqual(sum(self.report["terminal_histogram"].values()), count)
        self.assertTrue(all(
            sum(histogram.values()) == count
            for histogram in self.report["width_terminal_histograms"].values()
        ))
        self.assertEqual(len(self.report["intrinsic_core_carrier_adjacency"]), 30)
        self.assertTrue(all(
            item["status"] == "core_merges_carrier"
            for item in self.report["intrinsic_core_carrier_adjacency"]
        ))

    def test_materialized_choices_replay(self) -> None:
        for chain in self.report["chains"]:
            for k, evaluation in zip((7, 8, 9), chain["width_evaluations"]):
                self.assertEqual(replay_choice(k, chain["choice"]), evaluation)

    def test_status_and_one_next_topology(self) -> None:
        if self.report["survivors"]:
            self.assertEqual(self.report["status"], "stable_realization")
        else:
            self.assertEqual(
                self.report["status"],
                "complete_borrowed_leaf_bypass_obstruction",
            )
            self.assertEqual(self.report["next_topology"]["name"], "two-layer dogleg bypass")


if __name__ == "__main__":
    unittest.main()
