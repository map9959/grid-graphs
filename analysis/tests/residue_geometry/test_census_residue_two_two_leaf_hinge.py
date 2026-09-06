from __future__ import annotations

import unittest

from analysis.residue_geometry.census_residue_two_two_leaf_hinge import (
    SCHEMA,
    build_report,
    derive_hinge_types,
    replay_hinge,
)


class ResidueTwoTwoLeafHingeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.report = build_report()

    def test_seven_witnesses_derive_only_two_leaf_hinges(self) -> None:
        derivation = derive_hinge_types()
        self.assertEqual(derivation["source_witness_count"], 7)
        self.assertEqual(len(derivation["derived_types"]), 2)
        self.assertEqual(len(derivation["excluded_witnesses"]), 5)

    def test_grammar_has_one_rigid_chain_per_derived_type(self) -> None:
        self.assertEqual(self.report["grammar"]["chain_count"], 2)
        self.assertEqual(sum(self.report["terminal_histogram"].values()), 2)
        self.assertTrue(all(
            sum(histogram.values()) == 2
            for histogram in self.report["width_terminal_histograms"].values()
        ))

    def test_all_width_evaluations_replay(self) -> None:
        for chain in self.report["chains"]:
            for evaluation in chain["width_evaluations"]:
                replay = replay_hinge(
                    evaluation["k"],
                    evaluation["carrier"],
                    evaluation["side"],
                    evaluation["blocker"],
                    evaluation["hinge"],
                    tuple(evaluation["rigid_translation"]),
                )
                self.assertEqual(replay, evaluation)

    def test_complete_obstruction_and_next_topology(self) -> None:
        self.assertEqual(self.report["schema"], SCHEMA)
        self.assertEqual(self.report["status"], "complete_two_leaf_hinge_obstruction")
        self.assertFalse(self.report["survivors"])
        self.assertEqual(
            self.report["next_topology"]["name"],
            "nonleaf-spine split bypass",
        )


if __name__ == "__main__":
    unittest.main()
