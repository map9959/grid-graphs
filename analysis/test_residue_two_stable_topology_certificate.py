from __future__ import annotations

import unittest
from dataclasses import replace

from residue_two_affine_motif_grammar import (
    BoundaryDefectWord,
    CompactBoundaryDefectFrontier,
    PacketCarrierRole,
    expand_compact_boundary_defect_frontier,
)
from residue_two_compact_transition import ActionKey, ControlKey
from residue_two_stable_topology_certificate import (
    TopologyCertificateError,
    certify_topology,
    stable_topology_certificates,
)
from tile_grammar import advance_row


def _endpoint_values(dominant, exceptions, length):
    values = [dominant] * length
    for endpoint, value in exceptions:
        index = int(endpoint[1]) if endpoint[0] == "L" else length - 1 - int(endpoint[1])
        values[index] = value
    return tuple(values)


def _row_index(control: ControlKey, length: int) -> int:
    n = 3 * length + 2
    if control.cap_mode == "top":
        return 0
    if control.cap_mode == "bottom":
        return n - 1
    if control.cap_mode == "closed":
        return n
    return next(index for index in range(1, n - 1) if index % 3 == control.row_phase)


def _expand(control: ControlKey, length: int, row_index: int):
    atoms = _endpoint_values(
        control.dominant,
        tuple((item.endpoint, item.atom) for item in control.exceptions),
        length,
    )
    return expand_compact_boundary_defect_frontier(
        CompactBoundaryDefectFrontier(
            row_index,
            control.previous_cap_bits,
            control.left_face_role,
            BoundaryDefectWord(
                length,
                control.dominant,
                tuple((i, atom) for i, atom in enumerate(atoms) if atom != control.dominant),
            ),
            0,
            0,
        )
    )


def _mask(action: ActionKey, length: int) -> int:
    packets = _endpoint_values(action.dominant_packet, action.exceptions, length)
    n = 3 * length + 2
    value = action.cap_bits[0]
    for index, packet in enumerate(packets):
        value |= packet << (1 + 3 * index)
    return value | (action.cap_bits[1] << (n - 1))


class ResidueTwoStableTopologyCertificateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.certificates = stable_topology_certificates()

    def test_all_19_rules_have_a_dominant_packet_self_loop(self) -> None:
        self.assertEqual(len(self.certificates), 19)
        self.assertTrue(all(item.prefix_state == item.loop_state for item in self.certificates))

    def test_advance_row_regression_at_base_next_and_cached_larger_lengths(self) -> None:
        # These are exactly n=23..119 from the existing affine cache.  They are
        # regression comparisons only; the self-loop test is the induction.
        for length in range(7, 40):
            for certificate in self.certificates:
                row_index = _row_index(certificate.source, length)
                source = _expand(certificate.source, length, row_index)
                target = _expand(certificate.target, length, row_index + 1)
                outgoing = advance_row(source, _mask(certificate.action, length))
                self.assertIsNotNone(outgoing)
                self.assertEqual(outgoing.partition, target.partition)
                self.assertEqual(outgoing.previous_u_mask, target.previous_u_mask)

    def test_action_topology_mutation_is_rejected(self) -> None:
        certificate = self.certificates[8]
        self.assertEqual(certificate.action.exceptions, ())
        self.assertEqual(certificate.target.exceptions, ())
        damaged_action = replace(
            certificate.action, dominant_packet=certificate.action.dominant_packet ^ 1
        )
        # Keep the claimed outgoing mask consistent, so rejection is caused by
        # graph connectivity rather than the preliminary mask check.
        damaged_target = replace(
            certificate.target,
            dominant=replace(
                certificate.target.dominant,
                previous_word=damaged_action.dominant_packet,
            ),
        )
        with self.assertRaises(TopologyCertificateError):
            certify_topology(certificate.source, damaged_action, damaged_target)

    def test_target_partition_mutation_is_rejected(self) -> None:
        certificate = self.certificates[0]
        atom = replace(
            certificate.target.dominant,
            rooted_restriction=(0, 0, 1),
            carrier_roles=(PacketCarrierRole(1, "single", False, False),),
        )
        damaged = replace(certificate.target, dominant=atom)
        with self.assertRaises(TopologyCertificateError):
            certify_topology(certificate.source, certificate.action, damaged)

    def test_source_partition_mutation_is_rejected(self) -> None:
        certificate = self.certificates[1]
        atom = replace(
            certificate.source.dominant,
            rooted_restriction=(0, 0, 0),
            carrier_roles=(),
        )
        damaged = replace(certificate.source, dominant=atom)
        with self.assertRaises(TopologyCertificateError):
            certify_topology(damaged, certificate.action, certificate.target)


if __name__ == "__main__":
    unittest.main()
