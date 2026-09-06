from __future__ import annotations

import unittest
from dataclasses import FrozenInstanceError
from fractions import Fraction

from analysis.patterns.diagonal_patterns import residue_two_affine_pattern, residue_two_explicit_pattern
from analysis.bounds.packet_weight_certificate import (
    PacketRowWeightCertificate,
    append_segment_exact,
    begin_row,
    verify_packet_row_weight,
)
from analysis.tiles.tile_grammar import (
    FrontierState,
    advance_row,
    initial_state,
    render_mask,
    row_mask,
)


ALL_THREE_BIT_PACKETS = {
    f"P{value}": render_mask(value, 3) for value in range(8)
}


def reachable_structural_states(n: int) -> tuple[FrontierState, ...]:
    states = [initial_state(n)]
    layer = states
    for _ in range(n):
        children: dict[tuple[int, int, tuple[int, ...]], FrontierState] = {}
        for incoming in layer:
            for mask in range(1 << n):
                outgoing = advance_row(incoming, mask)
                if outgoing is not None:
                    key = (
                        outgoing.row_index,
                        outgoing.previous_u_mask,
                        outgoing.partition,
                    )
                    children.setdefault(key, outgoing)
        layer = list(children.values())
        states.extend(layer)
    return tuple(states)


class PacketWeightCertificateTests(unittest.TestCase):
    def test_all_n5_reachable_structural_states_and_masks(self) -> None:
        checked = 0
        for incoming in reachable_structural_states(5):
            if incoming.finished:
                continue
            for mask in range(1 << 5):
                row = render_mask(mask, 5)
                name = f"P{(mask >> 1) & 7}"
                with self.subTest(row_index=incoming.row_index, mask=mask):
                    certificate = verify_packet_row_weight(
                        incoming, row[:1], (name,), row[-1:], ALL_THREE_BIT_PACKETS
                    )
                    direct = advance_row(incoming, mask)
                    self.assertEqual(
                        certificate.outgoing if certificate is not None else None,
                        direct,
                    )
                    if certificate is not None:
                        self.assertEqual(certificate.totals.dU, mask.bit_count())
                        self.assertEqual(
                            certificate.totals.working_debt_delta,
                            certificate.debt_out - certificate.debt_in,
                        )
                        self.assertEqual(certificate.steps[-1].kind, "row_close")
                        self.assertEqual(certificate.steps[-1].charge, Fraction(1))
                        self.assertTrue(
                            all(not step.charge for step in certificate.steps[:-1])
                        )
                checked += 1
        self.assertGreater(checked, 32)

    def test_known_larger_witness_rows(self) -> None:
        for n in (8, 11, 14, 17):
            rows = (
                residue_two_explicit_pattern(n)
                if n in (8, 11, 14)
                else residue_two_affine_pattern(n)
            )
            incoming = initial_state(n)
            for row in rows:
                names = tuple(
                    next(
                        name
                        for name, bits in ALL_THREE_BIT_PACKETS.items()
                        if bits == row[start : start + 3]
                    )
                    for start in range(1, n - 1, 3)
                )
                certificate = PacketRowWeightCertificate.verify(
                    incoming, row[:1], names, row[-1:], ALL_THREE_BIT_PACKETS
                )
                self.assertIsNotNone(certificate)
                assert certificate is not None
                self.assertEqual(
                    certificate.outgoing, advance_row(incoming, row_mask(row))
                )
                incoming = certificate.outgoing

    def test_exact_segment_channels_and_immutability(self) -> None:
        incoming = advance_row(initial_state(5), row_mask("UUUUU"))
        assert incoming is not None
        cursor = begin_row(incoming)
        self.assertEqual(cursor.partial.columns, 0)
        prefix = append_segment_exact(cursor, "U", "prefix")
        assert prefix is not None
        packet = append_segment_exact(prefix.cursor, "U.U", "packet", "X")
        assert packet is not None
        self.assertEqual(packet.deltas.dU, 2)
        self.assertEqual(packet.deltas.dHorizontal, 1)
        self.assertEqual(packet.deltas.dVertical, 2)
        self.assertEqual(packet.deltas.dEdges, 3)
        self.assertEqual(
            packet.deltas.dRank, packet.deltas.dEdges - packet.deltas.dCycles
        )
        self.assertEqual(
            packet.deltas.weight,
            Fraction(3 * packet.deltas.dU - 2 * packet.deltas.dRank),
        )
        with self.assertRaises(FrozenInstanceError):
            packet.kind = "changed"  # type: ignore[misc]

    def test_charge_is_only_the_row_close_event(self) -> None:
        cursor = begin_row(initial_state(5))
        with self.assertRaisesRegex(ValueError, "only at row close"):
            append_segment_exact(cursor, ".", "prefix", charge=Fraction(1))
        with self.assertRaisesRegex(ValueError, "complete row"):
            append_segment_exact(cursor, "", "row_close", charge=Fraction(1))
        cursor_step = append_segment_exact(cursor, ".....", "suffix")
        assert cursor_step is not None
        with self.assertRaisesRegex(ValueError, "charge 1"):
            append_segment_exact(cursor_step.cursor, "", "row_close")
        close = append_segment_exact(
            cursor_step.cursor, "", "row_close", charge=Fraction(1)
        )
        assert close is not None
        self.assertEqual(close.deltas.weight, Fraction(-1))


if __name__ == "__main__":
    unittest.main()
