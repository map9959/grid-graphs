from __future__ import annotations

import unittest

from analysis.residue_geometry.census_residue_two_offset_spine_bypass import (
    SCHEMA,
    build_report,
    derive_offset_choices,
    replay_owner_census,
    replay_offset,
)


class ResidueTwoOffsetSpineBypassTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.report = build_report()

    def test_hard_capped_derivation(self) -> None:
        derivation = derive_offset_choices()
        self.assertEqual(len(derivation["types"]), 5)
        self.assertEqual(derivation["offset_attempts"], 10)
        represented_offsets = {
            (choice["type_index"], choice["offset_side"])
            for choice in derivation["choices"]
        }
        self.assertEqual(len(represented_offsets) + len(derivation["rejected_offsets"]), 10)
        for record in derivation["rejected_offsets"]:
            self.assertEqual(len(record["owner_equation_censuses"]), 3)
            for census in record["owner_equation_censuses"]:
                self.assertEqual(
                    replay_owner_census(
                        census["k"], record["type_index"], record["offset_side"]
                    ),
                    census,
                )

    def test_every_transported_choice_is_classified(self) -> None:
        count = self.report["grammar"]["transported_connector_choices"]
        self.assertEqual(len(self.report["chains"]), count)
        self.assertEqual(sum(self.report["terminal_histogram"].values()), count)
        self.assertTrue(all(
            sum(histogram.values()) == count
            for histogram in self.report["width_terminal_histograms"].values()
        ))

    def test_every_evaluation_replays(self) -> None:
        for chain in self.report["chains"]:
            for k, evaluation in zip((7, 8, 9), chain["width_evaluations"]):
                self.assertEqual(replay_offset(k, chain["choice"]), evaluation)

    def test_complete_status_or_verified_survivor(self) -> None:
        if self.report["survivors"]:
            self.assertEqual(self.report["status"], "stable_realization")
        else:
            self.assertEqual(
                self.report["status"],
                "complete_offset_spine_bypass_obstruction",
            )
            self.assertEqual(
                self.report["next_topology"]["name"],
                "borrowed-leaf offset bypass",
            )


if __name__ == "__main__":
    unittest.main()
