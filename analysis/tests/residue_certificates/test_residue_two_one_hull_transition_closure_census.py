from __future__ import annotations

import unittest

from analysis.residue_certificates.residue_two_one_hull_transition_closure_census import (
    HARD_DEPTH_GUARD,
    HARD_STATE_CAP,
    HARD_TRANSITION_CAP,
    _replay_defect,
    run_census,
)
from analysis.tiles.tile_grammar import row_mask


class ResidueTwoOneHullTransitionClosureCensusTests(unittest.TestCase):
    def test_small_state_cap_is_fast_deterministic_and_honest(self) -> None:
        arguments = {"state_cap": 2, "transition_cap": 64, "depth_guard": 5}
        first = run_census(**arguments)
        second = run_census(**arguments)
        self.assertEqual(first, second)
        self.assertEqual(first["status"], "incomplete_due_to_cap")
        self.assertEqual(first["limits"]["cap_hit"], "state_cap")
        self.assertEqual(first["counts"]["normalized_structural_states"], 2)
        self.assertEqual(first["coverage"]["action_packet_alphabet"], list(range(8)))
        self.assertTrue(first["coverage"]["finite_structural_atom_alphabet_available"])
        self.assertFalse(
            first["coverage"]["arbitrary_symbolic_word_successor_generation_available"]
        )
        self.assertFalse(first["coverage"]["arbitrary_width_closure_claimed"])
        self.assertIsNone(first["limits"]["beam_or_lossy_pruning"])

    def test_hard_defaults_cannot_be_overridden_upward(self) -> None:
        with self.assertRaises(ValueError):
            run_census(state_cap=HARD_STATE_CAP + 1)
        with self.assertRaises(ValueError):
            run_census(transition_cap=HARD_TRANSITION_CAP + 1)
        with self.assertRaises(ValueError):
            run_census(depth_guard=HARD_DEPTH_GUARD + 1)

    def test_n8_two_hull_defect_replays_independently(self) -> None:
        rows = (
            "........",
            "UUUUUUUU",
            "U.UUUUU.",
            "UUU.U.UU",
            "..UUUUU.",
        )
        replay = _replay_defect(8, tuple(row_mask(row) for row in rows))
        self.assertTrue(replay["verified"])
        self.assertEqual(replay["target_maximum_face_cut_width"], 2)
        self.assertEqual(replay["target_reason"], "concurrent occurrence hulls")


if __name__ == "__main__":
    unittest.main()
