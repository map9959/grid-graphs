from __future__ import annotations

import json
import unittest

from analysis.residue_certificates.residue_two_attachment_history import DEFAULT_OUTPUT, build_analysis
from analysis.tiles.tile_grammar import advance_row, initial_state
from analysis.tests._support import migrated_artifact


class AttachmentHistoryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.fresh = build_analysis()
        cls.cached = migrated_artifact(json.loads(DEFAULT_OUTPUT.read_text()))

    def test_cached_exact_regeneration(self) -> None:
        self.assertEqual(self.fresh, self.cached)

    def test_terminal_survivor_debt_and_capacity(self) -> None:
        terminal = self.fresh["terminal_178"]
        self.assertEqual(terminal["state_count"], 20)
        self.assertEqual(terminal["capacity_counts"], {"0": 2, "1": 18})
        self.assertTrue(all(state["rooted_debt"] == 2 for state in terminal["states"]))
        self.assertTrue(all(state["accepted_suffix_count"] == 0 for state in terminal["states"]))

    def test_matched_mask_exactly_discriminates_terminal_capacity(self) -> None:
        for state in self.fresh["terminal_178"]["states"]:
            chosen = next(
                outcome
                for outcome in state["suffix_outcomes"]
                if outcome["choices"] and outcome["choices"][0] is True
            )
            expected_mask = 2 if state["budgeted_merge_capacity"] else 0
            self.assertEqual(chosen["matched_neighbor_masks"][0], expected_mask)

    def test_179_suffix_pays_its_one_debt(self) -> None:
        suffix = self.fresh["witness_179_suffix"]
        self.assertEqual((suffix["rooted_debt"], suffix["remaining_u_budget"]), (1, 1))
        self.assertEqual((suffix["budgeted_merge_capacity"], suffix["accepted_suffix_count"]), (1, 1))
        accepted = next(item for item in suffix["suffix_outcomes"] if item["accepted"])
        self.assertEqual(accepted["choices"], [True, False])
        self.assertEqual(accepted["matched_neighbor_masks"], [2, 0])

    def test_all_explicit_row_histories_are_complete_and_close_debt(self) -> None:
        histories = self.fresh["explicit_witness_histories"]
        self.assertEqual(set(histories), {"5", "8", "11", "14", "17"})
        self.assertEqual([histories[str(n)]["u_count"] for n in (5, 8, 11, 14, 17)], [14, 37, 72, 119, 179])
        for n in (5, 8, 11, 14, 17):
            boundaries = histories[str(n)]["row_boundaries"]
            self.assertEqual(len(boundaries), n + 1)
            self.assertEqual(boundaries[0]["rooted_debt"], 0)
            self.assertEqual(boundaries[-1]["rooted_debt"], 0)
            self.assertEqual(boundaries[-1]["components"], 1)

    def test_cell_replay_matches_row_grammar_at_every_row_boundary(self) -> None:
        for n, record in self.fresh["explicit_witness_histories"].items():
            width = int(n)
            state = initial_state(width)
            for boundary in record["row_boundaries"][1:]:
                outgoing = advance_row(state, boundary["row_u_mask"])
                self.assertIsNotNone(outgoing)
                state = outgoing
                out_label = state.partition[0]
                self.assertEqual(boundary["u_cost"], state.u_cost)
                self.assertEqual(boundary["components"], len(set(state.partition)))
                self.assertEqual(
                    boundary["rooted_debt"],
                    len(set(state.partition) - {out_label}),
                )

    def test_missing_survivor_predecessors_are_explicitly_recorded(self) -> None:
        limitations = " ".join(self.fresh["limitations"])
        self.assertIn("no predecessor identities", limitations)
        self.assertIn("no row-boundary prefix history", limitations)


if __name__ == "__main__":
    unittest.main()
