from __future__ import annotations

import os
import unittest
from dataclasses import FrozenInstanceError, replace

from diagonal_patterns import residue_two_affine_pattern, residue_two_explicit_pattern
from equality_corridor import build_equality_corridor
from symbolic_packet_frontier import (
    SymbolicPacketFrontier,
    advance_symbolic_row,
    decode_frontier,
    encode_frontier,
)
from tile_grammar import FrontierState, advance_row, initial_state, row_mask


def split_mask(mask: int, n: int) -> tuple[int, tuple[int, ...], int]:
    return (
        mask & 1,
        tuple((mask >> (1 + 3 * packet)) & 7 for packet in range((n - 2) // 3)),
        (mask >> (n - 1)) & 1,
    )


class SymbolicPacketFrontierTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.corridor5 = build_equality_corridor(5)
        cls.corridor8 = None

    @classmethod
    def get_corridor8(cls):
        if cls.corridor8 is None:
            cls.corridor8 = build_equality_corridor(8)
        return cls.corridor8

    def assert_symbolic_transition(self, incoming: FrontierState, mask: int) -> None:
        symbolic = encode_frontier(incoming)
        actual = advance_symbolic_row(symbolic, *split_mask(mask, incoming.n))
        direct = advance_row(incoming, mask)
        self.assertEqual(decode_frontier(actual) if actual is not None else None, direct)

    def test_exact_round_trip_all_n5_equality_corridor_states(self) -> None:
        for row, keys in enumerate(self.corridor5.corridor_states):
            for key in keys:
                state = self.corridor5.layers[row][key]
                symbolic = encode_frontier(state)
                self.assertEqual(symbolic.width, 5)
                self.assertEqual(symbolic.packet_count, 1)
                self.assertEqual(decode_frontier(symbolic), state)

    @unittest.skipUnless(os.environ.get("GRID_GRAPHS_SLOW"), "slow exact n=8 corridor")
    def test_exact_round_trip_all_n8_equality_corridor_states(self) -> None:
        corridor = self.get_corridor8()
        for row, keys in enumerate(corridor.corridor_states):
            for key in keys:
                state = corridor.layers[row][key]
                symbolic = encode_frontier(state)
                self.assertEqual(symbolic.width, 8)
                self.assertEqual(symbolic.packet_count, 2)
                self.assertEqual(decode_frontier(symbolic), state)

    def test_every_mask_from_every_reachable_n5_structural_state(self) -> None:
        layers = [{(0, 0, (0,)): initial_state(5)}]
        for _ in range(5):
            children: dict[tuple[int, int, tuple[int, ...]], FrontierState] = {}
            for state in layers[-1].values():
                for mask in range(1 << 5):
                    outgoing = advance_row(state, mask)
                    if outgoing is not None:
                        key = (outgoing.row_index, outgoing.previous_u_mask, outgoing.partition)
                        children.setdefault(key, outgoing)
            layers.append(children)

        for layer in layers[:-1]:
            for state in layer.values():
                for mask in range(1 << 5):
                    with self.subTest(row=state.row_index, partition=state.partition, mask=mask):
                        self.assert_symbolic_transition(state, mask)

    @unittest.skipUnless(os.environ.get("GRID_GRAPHS_SLOW"), "slow exact n=8 corridor")
    def test_all_n8_corridor_edges_match_exact_transition(self) -> None:
        corridor = self.get_corridor8()
        for edges in corridor.corridor_edges:
            for edge in edges:
                incoming = corridor.layers[edge.row][edge.incoming]
                with self.subTest(row=edge.row, mask=edge.mask, incoming=edge.incoming):
                    self.assert_symbolic_transition(incoming, edge.mask)

    def test_fixed_n11_n14_n17_witness_rows(self) -> None:
        for n, rows in (
            (11, residue_two_explicit_pattern(11)),
            (14, residue_two_explicit_pattern(14)),
            (17, residue_two_affine_pattern(17)),
        ):
            incoming = initial_state(n)
            for row in rows:
                mask = row_mask(row)
                with self.subTest(n=n, row_index=incoming.row_index, row=row):
                    self.assert_symbolic_transition(incoming, mask)
                outgoing = advance_row(incoming, mask)
                self.assertIsNotNone(outgoing)
                assert outgoing is not None
                incoming = outgoing

    def test_immutable_and_malformed_dimensions_and_words(self) -> None:
        symbolic = encode_frontier(initial_state(5))
        with self.assertRaises(FrozenInstanceError):
            symbolic.row_index = 1  # type: ignore[misc]
        with self.assertRaisesRegex(ValueError, "packet count"):
            advance_symbolic_row(symbolic, 0, (), 0)
        with self.assertRaisesRegex(ValueError, "three-bit"):
            advance_symbolic_row(symbolic, 0, (8,), 0)
        with self.assertRaisesRegex(ValueError, "left cap"):
            advance_symbolic_row(symbolic, 2, (0,), 0)
        with self.assertRaisesRegex(ValueError, "form n"):
            encode_frontier(initial_state(6))
        with self.assertRaisesRegex(ValueError, "wrong size"):
            encode_frontier(FrontierState(5, 1, 0, (0,), 0, 0))
        with self.assertRaisesRegex(ValueError, "canonically rooted"):
            encode_frontier(FrontierState(5, 1, 0, (0, 2, 0, 2, 0), 0, 0))

    def test_symbolic_label_canonical_and_boundary_validation(self) -> None:
        open_state = encode_frontier(advance_row(initial_state(5), 0) or initial_state(5))
        with self.assertRaisesRegex(ValueError, "canonical"):
            replace(open_state, left_face_label=2)
        with self.assertRaisesRegex(ValueError, "groups do not match"):
            replace(open_state, packet_face_labels=())
        with self.assertRaisesRegex(ValueError, "cannot contain face labels"):
            replace(encode_frontier(initial_state(5)), left_face_label=0)
        with self.assertRaisesRegex(ValueError, "previous-row bits must be zero"):
            replace(encode_frontier(initial_state(5)), previous_cap_bits=(1, 0))
        with self.assertRaisesRegex(ValueError, "immutable three-face"):
            replace(open_state, packet_face_labels=((0, 0),))  # type: ignore[arg-type]


if __name__ == "__main__":
    unittest.main()
