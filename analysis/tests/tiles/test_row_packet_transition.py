from __future__ import annotations

import unittest
from dataclasses import FrozenInstanceError

from analysis.patterns.diagonal_patterns import (
    residue_two_affine_pattern,
    residue_two_explicit_pattern,
)
from analysis.tiles.row_packet_transition import (
    PacketRowCursor,
    append_packet,
    finish_row,
    start_row,
    verify_packet_row,
)
from analysis.tiles.tile_grammar import (
    FrontierState,
    advance_row,
    initial_state,
    row_mask,
)

ALL_THREE_BIT_PACKETS = {
    f"P{value}": "".join(
        "U" if value & (1 << column) else "." for column in range(3)
    )
    for value in range(8)
}


class RowPacketTransitionTests(unittest.TestCase):
    def assert_matches_advance_row(
        self,
        incoming: FrontierState,
        row: str,
    ) -> None:
        names = tuple(
            next(name for name, value in ALL_THREE_BIT_PACKETS.items() if value == row[start:start + 3])
            for start in range(1, len(row) - 1, 3)
        )
        checkpoints, transition = verify_packet_row(
            incoming, row[0], names, row[-1], ALL_THREE_BIT_PACKETS
        )
        direct = advance_row(incoming, row_mask(row))
        self.assertEqual(transition.outgoing if transition is not None else None, direct)
        if transition is None:
            return
        self.assertEqual(len(checkpoints), len(names) + 1)
        self.assertEqual(transition.row_mask, row_mask(row))
        self.assertEqual(transition.packet_names, names)
        self.assertEqual(
            transition.packet_charge,
            sum(ALL_THREE_BIT_PACKETS[name].count("U") - 2 for name in names),
        )
        self.assertEqual(
            transition.h_count,
            sum(ALL_THREE_BIT_PACKETS[name] == "UUU" for name in names),
        )
        self.assertEqual(checkpoints[-1].u_cost, incoming.u_cost + row[:-1].count("U"))
        self.assertEqual(
            checkpoints[-1].cycle_excess,
            incoming.cycle_excess + checkpoints[-1].partial.cycle_excess,
        )

    def test_all_three_bit_packets_at_every_n5_first_row_frontier(self) -> None:
        incoming_states = [initial_state(5)]
        for previous_mask in range(1 << 5):
            incoming = advance_row(initial_state(5), previous_mask)
            assert incoming is not None
            incoming_states.append(incoming)
        for incoming in incoming_states:
            for packet in ALL_THREE_BIT_PACKETS.values():
                with self.subTest(incoming=incoming, packet=packet):
                    self.assert_matches_advance_row(incoming, f".{packet}.")

    def test_fixed_witness_rows_at_larger_widths(self) -> None:
        for n in (8, 11, 14, 17):
            rows = (
                residue_two_explicit_pattern(n)
                if n in (8, 11, 14)
                else residue_two_affine_pattern(n)
            )
            incoming = initial_state(n)
            for row in rows:
                with self.subTest(n=n, row=row):
                    self.assert_matches_advance_row(incoming, row)
                outgoing = advance_row(incoming, row_mask(row))
                self.assertIsNotNone(outgoing)
                assert outgoing is not None
                incoming = outgoing

    def test_cursor_is_immutable_and_cumulative(self) -> None:
        incoming = advance_row(initial_state(5), row_mask("UUUUU"))
        assert incoming is not None
        cursor = start_row(incoming, ".")
        assert cursor is not None
        self.assertIsInstance(cursor, PacketRowCursor)
        self.assertEqual(cursor.u_cost, incoming.u_cost)
        self.assertEqual(cursor.cycle_excess, incoming.cycle_excess)
        with self.assertRaises(FrozenInstanceError):
            cursor.partial = cursor.partial  # type: ignore[misc]

    def test_bottom_closure_and_sealing_return_none(self) -> None:
        sealed_case = None
        bottom_case = None
        for previous_mask in range(1 << 5):
            incoming = advance_row(initial_state(5), previous_mask)
            assert incoming is not None
            for current_mask in range(1 << 5):
                row = "".join("U" if current_mask & (1 << c) else "." for c in range(5))
                checkpoints, transition = verify_packet_row(
                    incoming, row[0], ("packet",), row[-1], {"packet": row[1:4]}
                )
                if transition is None and checkpoints:
                    sealed_case = (incoming, row)
                    break
            if sealed_case is not None:
                break
        self.assertIsNotNone(sealed_case)

        incoming = initial_state(5)
        for mask in (0, 31, 13, 13):
            incoming = advance_row(incoming, mask)
            assert incoming is not None
        for current_mask in range(1 << 5):
            row = "".join("U" if current_mask & (1 << c) else "." for c in range(5))
            direct = advance_row(incoming, current_mask)
            checkpoints, transition = verify_packet_row(
                incoming, row[0], ("packet",), row[-1], {"packet": row[1:4]}
            )
            if direct is None and checkpoints:
                bottom_case = row
                self.assertIsNone(transition)
                break
        self.assertIsNotNone(bottom_case)

    def test_malformed_dimensions_names_and_bits_raise(self) -> None:
        incoming = initial_state(5)
        cursor = start_row(incoming, ".")
        assert cursor is not None
        with self.assertRaisesRegex(ValueError, "unknown packet name"):
            append_packet(cursor, "missing", ALL_THREE_BIT_PACKETS)
        with self.assertRaisesRegex(ValueError, "span the grid width"):
            finish_row(cursor, ".")
        with self.assertRaisesRegex(ValueError, "beyond the grid width"):
            finish_row(cursor, ".....")
        with self.assertRaisesRegex(ValueError, "only.*U"):
            start_row(incoming, "X")
        with self.assertRaisesRegex(ValueError, "span the grid width"):
            verify_packet_row(incoming, ".", (), ".", ALL_THREE_BIT_PACKETS)
        with self.assertRaisesRegex(ValueError, "unknown packet names"):
            verify_packet_row(incoming, ".", ("missing",), ".", ALL_THREE_BIT_PACKETS)
        finished = FrontierState(5, 5, 0, (0,), 0, 0)
        with self.assertRaisesRegex(ValueError, "finished frontier"):
            start_row(finished, "")


if __name__ == "__main__":
    unittest.main()
