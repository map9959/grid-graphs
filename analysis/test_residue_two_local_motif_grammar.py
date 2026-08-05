from __future__ import annotations

import json
import os
import unittest
from pathlib import Path

from residue_two_local_motif_grammar import (
    all_rooted_triple_symbols,
    build_artifact,
    face_cut_open_widths,
    grammar_acceptance,
    packet_motif_symbols,
)
from tile_grammar import FrontierState


ARTIFACT = Path(__file__).with_name("residue_two_local_motif_grammar.json")
ALPHABET = frozenset(
    {
        (),
        (0, 0, 0), (0, 0, 1), (0, 1, 1), (0, 1, 2),
        (1, 0, 0), (1, 0, 2), (1, 1, 0), (1, 1, 1), (1, 1, 2),
        (1, 2, 0), (1, 2, 2), (1, 2, 3),
    }
)


class ResidueTwoLocalMotifGrammarTests(unittest.TestCase):
    def test_exact_rooted_alphabet_and_exclusions(self) -> None:
        universe = set(all_rooted_triple_symbols())
        self.assertEqual(len(universe), 15)
        self.assertEqual(universe - ALPHABET, {(0, 1, 0), (1, 0, 1), (1, 2, 1)})

    def test_packet_restrictions_are_independently_rooted(self) -> None:
        state = FrontierState(8, 3, 0, (0, 1, 2, 2, 0, 4, 5, 4), 0, 0)
        self.assertEqual(packet_motif_symbols(state), ((1, 1, 0), (1, 2, 1)))
        with self.assertRaises(ValueError):
            packet_motif_symbols(FrontierState(7, 0, 0, (0,), 0, 0))

    def test_face_cut_refines_combined_grammar(self) -> None:
        state = FrontierState(8, 5, 126, (0, 1, 2, 3, 3, 2, 2, 4), 25, 2)
        decisions = grammar_acceptance(state, ALPHABET)
        self.assertTrue(decisions["carrier_only"])
        self.assertTrue(decisions["local_motifs_only"])
        self.assertTrue(decisions["combined"])
        self.assertFalse(decisions["combined_face_cut"])
        self.assertEqual(max(face_cut_open_widths(state)), 2)

    def test_cached_artifact_reports_exact_finite_censuses(self) -> None:
        artifact = json.loads(ARTIFACT.read_text())
        self.assertFalse(artifact["scope"]["theorem_or_certificate"])
        self.assertEqual(artifact["scope"]["complete_training_corridors"], [5, 8])
        self.assertEqual(
            [item["id"] for item in artifact["alphabet"]["excluded"]],
            ["010", "101", "121"],
        )
        self.assertEqual(len(artifact["alphabet"]["allowed"]), 13)
        expected = {
            "n5-complete-equality-corridor": (117, 117, 117, 117, 117),
            "n8-complete-equality-corridor": (208, 208, 208, 208, 208),
            "n5-full-structurally-reachable-layers": (369, 369, 363, 363, 363),
            "n8-full-structurally-reachable-layers": (14582, 14465, 14266, 14149, 14134),
            "n11-fixed-equality-trace": (12, 12, 12, 12, 12),
            "n14-fixed-equality-trace": (15, 15, 15, 15, 15),
            "n17-fixed-near-equality-179-U-trace": (18, 18, 18, 18, 18),
        }
        for source, counts in expected.items():
            record = artifact["sources"][source]
            actual = (record["states"], *(record["grammars"][name]["accepted"] for name in (
                "carrier_only", "local_motifs_only", "combined", "combined_face_cut"
            )))
            self.assertEqual(actual, counts)
        for width in ("5", "8"):
            for grammar in artifact["row_transitions"][width].values():
                self.assertTrue(grammar["retains_all_equality_edges"])
                self.assertEqual(
                    grammar["staying_in_grammar"] + grammar["leaving_grammar"],
                    grammar["frontier_accepted_transitions"],
                )

    @unittest.skipUnless(os.environ.get("GRID_GRAPHS_SLOW"), "slow exact regeneration")
    def test_cached_artifact_regenerates_exactly(self) -> None:
        self.assertEqual(build_artifact(), json.loads(ARTIFACT.read_text()))


if __name__ == "__main__":
    unittest.main()
