from __future__ import annotations

import unittest

from census_residue_two_endpoint_slide import (
    SCHEMA,
    TRANSLATIONS,
    build_report,
    derive_pair_types,
    replay_slide,
)


class ResidueTwoEndpointSlideTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.report = build_report()

    def test_pair_grammar_is_exactly_derived_and_hard_capped(self) -> None:
        pairs = derive_pair_types()
        self.assertEqual(len(pairs), 20)
        self.assertTrue(all(pair["blocker_length"] in (1, 2) for pair in pairs))
        self.assertEqual(len(TRANSLATIONS), 4)
        self.assertEqual(self.report["grammar"]["chain_count"], 80)

    def test_every_chain_is_classified(self) -> None:
        self.assertEqual(sum(self.report["terminal_histogram"].values()), 80)
        self.assertEqual(len(self.report["chains"]), 80)
        self.assertTrue(all(
            sum(histogram.values()) == 80
            for histogram in self.report["width_terminal_histograms"].values()
        ))

    def test_terminal_width_records_replay(self) -> None:
        for chain in self.report["chains"]:
            pair = chain["pair"]
            delta = tuple(chain["translation"])
            for evaluation in chain["width_evaluations"]:
                replay = replay_slide(
                    evaluation["k"],
                    evaluation["carrier"],
                    pair["side"],
                    evaluation["blocker"],
                    delta,
                )
                self.assertEqual(replay, evaluation)

    def test_report_status_and_next_topology(self) -> None:
        self.assertEqual(self.report["schema"], SCHEMA)
        self.assertEqual(self.report["status"], "complete_endpoint_slide_obstruction")
        self.assertFalse(self.report["survivors"])
        self.assertEqual(self.report["next_topology"]["name"], "two-leaf hinge exchange")


if __name__ == "__main__":
    unittest.main()
