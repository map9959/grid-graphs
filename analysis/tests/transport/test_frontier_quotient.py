from __future__ import annotations

import unittest
from dataclasses import replace

from analysis.patterns.diagonal_patterns import residue_zero_explicit_pattern
from analysis.transport.frontier_quotient import replace_slab_tile
from analysis.transport.open_slab_signature import restore_open_slab_state, verify_open_slab_round_trip
from analysis.tiles.tile_grammar import (
    advance_band,
    initial_state,
    production_tiles,
    projected_frontier_key,
    row_mask,
)


class OpenSlabSignatureTests(unittest.TestCase):
    def test_known_naive_collision_is_losslessly_separated(self) -> None:
        n = 18
        slab_start = 4
        rows = residue_zero_explicit_pattern(n)
        tiles = {tile.name: tile for tile in production_tiles(oriented=True)}
        start = initial_state(n)
        state_02 = advance_band(
            start, replace_slab_tile(rows, 0, slab_start, tiles["O02"])
        )
        state_03 = advance_band(
            start, replace_slab_tile(rows, 0, slab_start, tiles["O03"])
        )
        self.assertIsNotNone(state_02)
        self.assertIsNotNone(state_03)
        if state_02 is None or state_03 is None:
            self.fail("known first-band states were unexpectedly sealed")

        naive_02 = projected_frontier_key(state_02, slab_start, 3, 5)
        naive_03 = projected_frontier_key(state_03, slab_start, 3, 6)
        self.assertEqual(naive_02, naive_03)
        self.assertEqual(
            naive_02,
            (
                3,
                16374,
                (0, 1, 2, 3, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6),
                27,
                0,
            ),
        )

        signature_02 = verify_open_slab_round_trip(state_02, slab_start, 3, 5)
        signature_03 = verify_open_slab_round_trip(state_03, slab_start, 3, 6)
        self.assertEqual(signature_02.projected_partition, signature_03.projected_partition)
        self.assertNotEqual(signature_02.slab_previous_u_mask, signature_03.slab_previous_u_mask)
        self.assertNotEqual(signature_02.attachment_partition, signature_03.attachment_partition)
        self.assertEqual(signature_02.attachment_partition, tuple(range(10)))
        self.assertEqual(
            signature_03.attachment_partition,
            (0, 1, 2, 3, 4, 5, 6, 5, 5, 5),
        )

        child_02 = advance_band(
            state_02, replace_slab_tile(rows, 1, slab_start, tiles["O20"])
        )
        child_03 = advance_band(
            state_03, replace_slab_tile(rows, 1, slab_start, tiles["O20"])
        )
        self.assertIsNotNone(child_02)
        self.assertIsNotNone(child_03)
        if child_02 is None or child_03 is None:
            self.fail("known continuation was unexpectedly sealed")
        child_signature_02 = verify_open_slab_round_trip(child_02, slab_start, 3, 11)
        child_signature_03 = verify_open_slab_round_trip(child_03, slab_start, 3, 12)
        self.assertEqual(child_signature_02.compressed_previous_u_mask, 14038)
        self.assertEqual(child_signature_03.compressed_previous_u_mask, 14038)
        self.assertEqual(child_signature_02.slab_previous_u_mask, 0b011)
        self.assertEqual(child_signature_03.slab_previous_u_mask, 0b011)
        self.assertEqual(child_signature_02.projected_partition, tuple(range(15)))
        self.assertEqual(child_signature_03.projected_partition, tuple(range(15)))
        self.assertNotEqual(
            child_signature_02.attachment_partition,
            child_signature_03.attachment_partition,
        )
        self.assertEqual((child_02.cycle_excess, child_03.cycle_excess), (1, 3))

    def test_invalid_slab_is_rejected(self) -> None:
        state = advance_band(
            initial_state(18),
            tuple(map(row_mask, residue_zero_explicit_pattern(18)[:3])),
        )
        self.assertIsNotNone(state)
        if state is None:
            self.fail("known first band was unexpectedly sealed")
        with self.assertRaisesRegex(ValueError, "beyond"):
            verify_open_slab_round_trip(state, 15, 3)

    def test_boundary_slabs_and_malformed_masks(self) -> None:
        state = advance_band(
            initial_state(18),
            tuple(map(row_mask, residue_zero_explicit_pattern(18)[:3])),
        )
        self.assertIsNotNone(state)
        if state is None:
            self.fail("known first band was unexpectedly sealed")
        left = verify_open_slab_round_trip(state, 0, 1)
        right = verify_open_slab_round_trip(state, 14, 3)
        self.assertEqual(restore_open_slab_state(left), state)
        self.assertEqual(restore_open_slab_state(right), state)
        for malformed in (
            replace(left, slab_previous_u_mask=-1),
            replace(left, compressed_previous_u_mask=-1),
            replace(left, compressed_previous_u_mask=1 << 17),
            replace(left, row_index=-1),
            replace(left, row_index=19),
            replace(left, original_n=1),
        ):
            with self.assertRaises(ValueError):
                restore_open_slab_state(malformed)


if __name__ == "__main__":
    unittest.main()
