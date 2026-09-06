from __future__ import annotations

import unittest

from analysis.transport.equality_corridor import build_equality_corridor
from analysis.residue_certificates.residue_two_local_motif_grammar import maximum_face_cut_open_width
from analysis.residue_certificates.residue_two_n11_grammar_counterexample import ROWS
from analysis.residue_certificates.residue_two_silent_hull_language import (
    SilentHullAtom,
    SilentHullFrontier,
    certify_silent_hull_transition,
    decode_silent_hull_frontier,
    encode_silent_hull_frontier,
    finite_structural_atom_alphabet,
)
from analysis.tiles.tile_grammar import advance_row, initial_state, row_mask


def split_mask(mask: int, n: int):
    return (
        (mask & 1, (mask >> (n - 1)) & 1),
        tuple((mask >> (1 + 3 * packet)) & 7 for packet in range((n - 2) // 3)),
    )


class ResidueTwoSilentHullLanguageTests(unittest.TestCase):
    def test_finite_atom_alphabet_contains_a_silent_symbol(self) -> None:
        alphabet = finite_structural_atom_alphabet()
        self.assertTrue(alphabet)
        self.assertTrue(any(atom.silent_carry for atom in alphabet))

    def test_all_complete_n5_equality_edges_round_trip_and_certify(self) -> None:
        corridor = build_equality_corridor(5)
        for row, keys in enumerate(corridor.corridor_states):
            for key in keys:
                state = corridor.layers[row][key]
                encoded = encode_silent_hull_frontier(state)
                self.assertEqual(decode_silent_hull_frontier(encoded), state)
        for edges in corridor.corridor_edges:
            for edge in edges:
                incoming = corridor.layers[edge.row][edge.incoming]
                # Corridor layers retain one structural representative, whose
                # cumulative counters need not belong to this particular edge.
                outgoing = advance_row(incoming, edge.mask)
                self.assertIsNotNone(outgoing)
                assert outgoing is not None
                caps, packets = split_mask(edge.mask, 5)
                counters = certify_silent_hull_transition(
                    encode_silent_hull_frontier(incoming),
                    caps,
                    packets,
                    encode_silent_hull_frontier(outgoing),
                )
                self.assertEqual(counters.weight, edge.weight)
                self.assertEqual(counters.cycles, edge.d_cycles)

    def test_n11_gap_is_a_silent_carrier_and_every_row_transition_certifies(self) -> None:
        state = initial_state(11)
        silent_rows = []
        for row_number, row in enumerate(ROWS, 1):
            outgoing = advance_row(state, row_mask(row))
            self.assertIsNotNone(outgoing)
            assert outgoing is not None
            source = encode_silent_hull_frontier(state)
            target = encode_silent_hull_frontier(outgoing)
            caps, packets = split_mask(row_mask(row), 11)
            certify_silent_hull_transition(source, caps, packets, target)
            if any(atom.silent_carry for atom in target.atoms):
                silent_rows.append(row_number)
            state = outgoing
        self.assertEqual(silent_rows, [8])

    def test_exact_conditional_coverage_on_all_n5_canonical_partitions(self) -> None:
        # Restricted-growth strings enumerate every rooted partition of four faces.
        words = [(0,)]
        for _ in range(3):
            words = [(*word, label) for word in words for label in range(max(word) + 2)]
        checked = 0
        for faces in words:
            state = initial_state(5)
            state = type(state)(5, 1, 0, (0, *faces), 0, 0)
            if maximum_face_cut_open_width(state) <= 1:
                encoded = encode_silent_hull_frontier(state)
                self.assertEqual(decode_silent_hull_frontier(encoded), state)
                checked += 1
        self.assertGreater(checked, 0)

    def test_row_shape_is_part_of_codec_validity(self) -> None:
        malformed = SilentHullFrontier(
            1, (0, 0), "absent", (SilentHullAtom(0, (), ()),), 0, 0
        )
        with self.assertRaisesRegex(ValueError, "row index"):
            decode_silent_hull_frontier(malformed)


if __name__ == "__main__":
    unittest.main()
