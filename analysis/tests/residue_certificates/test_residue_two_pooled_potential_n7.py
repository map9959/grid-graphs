from __future__ import annotations

import json
import os
import unittest


from analysis.residue_certificates.residue_two_pooled_potential_n7 import build_experiment
from analysis._paths import analysis_path
from analysis.tests._support import migrated_artifact


class ChargeOnePooledPotentialN7Tests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.result = migrated_artifact(json.loads(
            analysis_path("residue_two_pooled_potential_n8.json").read_text()
        ))

    def test_scope_is_explicitly_finite_and_n7_is_held_out_feature_diagnostic(self) -> None:
        scope = self.result["scope"]
        self.assertEqual(scope["widths"], [3, 4, 5, 6, 7, 8])
        self.assertEqual(scope["base_feature_level"], "runs")
        self.assertEqual(scope["feature_level"], "runs+rows_remaining")
        self.assertIn("negative constraint cycle", scope["refinement_reason"])
        self.assertEqual(scope["uniform_row_charge"], 1)
        self.assertIn("not-a-uniform-proof", scope["semantics"])
        self.assertEqual(scope["held_out_widths"], [7, 8])

    def test_every_reachable_n7_transition_is_enumerated(self) -> None:
        n7 = self.result["widths"]["7"]
        self.assertEqual(
            n7["reachable_states_by_row"],
            [1, 128, 497, 743, 930, 940, 940, 128],
        )
        self.assertEqual(n7["accepted_transitions"], 87_968)
        self.assertEqual(
            n7["attempted_transitions"],
            sum(n7["reachable_states_by_row"][:-1]) * 128,
        )

    def test_strongest_parallel_constraints_are_compact_and_hashed(self) -> None:
        census = self.result["census"]
        self.assertGreater(census["discarded_parallel_constraints"], 0)
        self.assertLess(
            census["pooled_strongest_transitions"],
            census["accepted_concrete_transitions"],
        )
        for digest in self.result["hashes"].values():
            self.assertEqual(len(digest), 64)
            int(digest, 16)

    def test_n8_falsifies_sharp_residue_two_pooled_constant(self) -> None:
        self.assertEqual(
            self.result["analysis"]["pooled_phase_terminal_constants"],
            {"0": [4, 1], "1": [2, 1], "2": [2, 1]},
        )
        self.assertFalse(self.result["analysis"]["known_minima_reproduced_all_widths"])
        self.assertFalse(self.result["analysis"]["held_out_widths_reproduce_known_minima"])
        self.assertFalse(
            self.result["analysis"]["residue_two_terminal_constant_survives_n8"]
        )
        self.assertTrue(self.result["widths"]["7"]["pooled_reproduces_known_minimum"])
        self.assertFalse(self.result["widths"]["8"]["pooled_reproduces_known_minimum"])
        self.assertEqual(self.result["analysis"]["potential_value_denominators"], [1])
        self.assertEqual(
            [
                self.result["widths"][str(n)]["pooled_implied_minimum_u"]
                for n in range(3, 9)
            ],
            [5, 8, 13, 20, 27, 36],
        )

    @unittest.skipUnless(os.environ.get("GRID_GRAPHS_SLOW"), "slow exact regeneration")
    def test_cached_artifact_regenerates_exactly(self) -> None:
        self.assertEqual(build_experiment(), self.result)


if __name__ == "__main__":
    unittest.main()
