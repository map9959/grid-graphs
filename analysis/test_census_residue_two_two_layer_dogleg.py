from __future__ import annotations

import unittest

from census_residue_two_two_layer_dogleg import (
    SCHEMA,
    build_report,
    derive_dogleg_choices,
    replay_choice,
)


class ResidueTwoTwoLayerDoglegTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.report = build_report()

    def test_final_grammar_hard_caps(self) -> None:
        derivation = derive_dogleg_choices()
        self.assertEqual(len(derivation["types"]), 5)
        self.assertEqual(len(derivation["attempts"]), 20)
        self.assertEqual(self.report["grammar"]["other_edits"], "none")

    def test_every_materialized_choice_is_classified(self) -> None:
        count = self.report["grammar"]["materialized_choices"]
        self.assertEqual(len(self.report["chains"]), count)
        self.assertEqual(sum(self.report["terminal_histogram"].values()), count)
        self.assertTrue(all(
            sum(histogram.values()) == count
            for histogram in self.report["width_terminal_histograms"].values()
        ))

    def test_materialized_choices_replay(self) -> None:
        for chain in self.report["chains"]:
            for k, evaluation in zip((7, 8, 9), chain["width_evaluations"]):
                self.assertEqual(replay_choice(k, chain["choice"]), evaluation)

    def test_terminal_status_has_no_invented_next_topology(self) -> None:
        if self.report["survivors"]:
            self.assertEqual(self.report["status"], "stable_realization")
        else:
            self.assertEqual(
                self.report["status"],
                "complete_two_layer_dogleg_obstruction",
            )
            self.assertTrue(
                self.report["line_status"]["affine_surgery_line_exhausted"]
            )
            self.assertIsNone(self.report["line_status"]["next_topology"])


if __name__ == "__main__":
    unittest.main()
