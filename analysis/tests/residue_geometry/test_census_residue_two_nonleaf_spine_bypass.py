from __future__ import annotations

import unittest

from analysis.residue_geometry.census_residue_two_nonleaf_spine_bypass import (
    SCHEMA,
    build_report,
    derive_bypass_types,
    replay_bypass,
)


class ResidueTwoNonleafSpineBypassTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.report = build_report()

    def test_exactly_five_witnesses_give_one_bypass_each(self) -> None:
        types = derive_bypass_types()
        self.assertEqual(len(types), 5)
        self.assertEqual(self.report["grammar"]["choices_per_witness"], 1)
        self.assertEqual(self.report["grammar"]["chain_count"], 5)

    def test_every_width_is_classified(self) -> None:
        self.assertEqual(sum(self.report["terminal_histogram"].values()), 5)
        self.assertTrue(all(
            sum(histogram.values()) == 5
            for histogram in self.report["width_terminal_histograms"].values()
        ))

    def test_all_evaluations_replay(self) -> None:
        for chain in self.report["chains"]:
            for evaluation in chain["width_evaluations"]:
                replay = replay_bypass(
                    evaluation["k"],
                    evaluation["carrier"],
                    evaluation["side"],
                    evaluation["blocker"],
                    evaluation["spine"],
                    tuple(evaluation["blocker_translation"]),
                )
                self.assertEqual(replay, evaluation)

    def test_complete_status_and_narrowed_topology(self) -> None:
        self.assertEqual(self.report["schema"], SCHEMA)
        self.assertEqual(
            self.report["status"],
            "complete_nonleaf_spine_bypass_obstruction",
        )
        self.assertFalse(self.report["survivors"])
        self.assertEqual(self.report["next_topology"]["name"], "offset spine bypass")


if __name__ == "__main__":
    unittest.main()
