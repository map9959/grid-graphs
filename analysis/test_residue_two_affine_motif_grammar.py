from __future__ import annotations

import json
import os
import unittest
from dataclasses import replace
from pathlib import Path

from diagonal_patterns import residue_two_affine_pattern
from residue_two_affine_motif_grammar import (
    BoundaryDefectAtom,
    BoundaryDefectWord,
    CompactBoundaryDefectFrontier,
    InteriorDefectError,
    build_artifact,
    canonical_dominant,
    encode_boundary_defect_frontier,
    encode_boundary_defect_word,
    encode_compact_boundary_defect_frontier,
    expand_boundary_defect_frontier,
    expand_boundary_defect_word,
    expand_compact_boundary_defect_frontier,
    replay_trace,
)


ARTIFACT = Path(__file__).with_name("residue_two_affine_motif_grammar.json")


def atom(word: int) -> BoundaryDefectAtom:
    return BoundaryDefectAtom(word, (0, 0, 0), ())


class ResidueTwoAffineMotifGrammarTests(unittest.TestCase):
    def test_canonical_exact_word_codec_and_tie_break(self) -> None:
        low, high = atom(1), atom(6)
        atoms = (high, low, low, low, low, high, high, high)
        encoded = encode_boundary_defect_word(atoms)
        self.assertEqual(encoded.dominant, low)
        self.assertEqual(tuple(index for index, _ in encoded.exceptions), (0, 5, 6, 7))
        self.assertEqual(expand_boundary_defect_word(encoded), atoms)
        self.assertEqual(canonical_dominant((high, low)), low)

    def test_interior_defects_and_noncanonical_records_are_rejected(self) -> None:
        dominant, defect = atom(2), atom(3)
        with self.assertRaisesRegex(InteriorDefectError, r"\(2,\)"):
            encode_boundary_defect_word((dominant, dominant, defect, dominant, dominant, dominant, dominant))
        broken = BoundaryDefectWord(7, dominant, ((2, defect),))
        with self.assertRaisesRegex(ValueError, "boundary indices"):
            expand_boundary_defect_word(broken)
        valid = encode_boundary_defect_word((defect, dominant, dominant, dominant, dominant, dominant))
        with self.assertRaisesRegex(ValueError, "canonical"):
            expand_boundary_defect_word(
                BoundaryDefectWord(
                    6,
                    dominant,
                    ((0, defect), (3, defect), (4, defect), (5, defect)),
                )
            )

    def test_symbolic_frontier_round_trip_uses_lossless_carrier_channel(self) -> None:
        trace = replay_trace(residue_two_affine_pattern(17))
        for state in trace:
            encoded = encode_boundary_defect_frontier(state)
            self.assertLessEqual(len(encoded.word.exceptions), 6)
            self.assertEqual(expand_boundary_defect_frontier(encoded), state)
        encoded = encode_boundary_defect_frontier(trace[8])
        with self.assertRaises(ValueError):
            expand_boundary_defect_frontier(
                replace(encoded, carrier_record=replace(encoded.carrier_record, events=()))
            )

    def test_compact_one_carrier_round_trip_needs_no_global_record(self) -> None:
        for n in (17, 20, 23, 32):
            for state in replay_trace(residue_two_affine_pattern(n)):
                encoded = encode_compact_boundary_defect_frontier(state)
                self.assertIsInstance(encoded, CompactBoundaryDefectFrontier)
                self.assertLessEqual(len(encoded.word.exceptions), 6)
                self.assertEqual(expand_compact_boundary_defect_frontier(encoded), state)

    def test_cached_artifact_reports_required_scope_and_censuses(self) -> None:
        artifact = json.loads(ARTIFACT.read_text())
        scope = artifact["scope"]
        self.assertTrue(scope["exact_codec"])
        self.assertEqual(scope["complete_equality_corridors"], [5, 8])
        self.assertEqual(scope["fixed_equality_traces"], [11, 14])
        self.assertEqual(scope["affine_generated_widths"], list(range(17, 120, 3)))
        self.assertFalse(scope["equality_language_coverage_proved"])
        for name, count in (
            ("n5-complete-equality-corridor", 117),
            ("n8-complete-equality-corridor", 208),
            ("n11-fixed-equality-trace", 12),
            ("n14-fixed-equality-trace", 15),
            ("n17-fixed-near-equality-179-U-trace", 18),
        ):
            source = artifact["sources"][name]
            self.assertEqual(source["states"], count)
            self.assertEqual(source["lossless_round_trips"], source["accepted"])
        for name in (
            "n5-complete-equality-corridor",
            "n8-complete-equality-corridor",
            "n11-fixed-equality-trace",
            "n14-fixed-equality-trace",
        ):
            self.assertTrue(artifact["sources"][name]["acceptance"])
        near = artifact["sources"]["n17-fixed-near-equality-179-U-trace"]
        self.assertEqual((near["accepted"], near["interior_violation_occurrences"]), (18, 0))
        affine = artifact["affine_family"]
        self.assertTrue(affine["all_generated_traces_accepted"])
        self.assertEqual(affine["states"], 2415)
        self.assertEqual(affine["maximum_exception_count"], 5)
        self.assertEqual(affine["interior_violation_occurrences"], 0)
        self.assertTrue(
            artifact["row_transition_closure"]["all_observed_adjacent_width_pairs_closed"]
        )

    @unittest.skipUnless(os.environ.get("GRID_GRAPHS_SLOW"), "slow exact regeneration")
    def test_cached_artifact_regenerates_exactly(self) -> None:
        self.assertEqual(build_artifact(), json.loads(ARTIFACT.read_text()))


if __name__ == "__main__":
    unittest.main()
