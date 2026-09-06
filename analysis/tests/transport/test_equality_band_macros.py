from __future__ import annotations

import unittest
from dataclasses import replace
from itertools import product

from analysis.bounds.proof_oriented_identities import tile_grammar_row_deltas
from analysis.tiles.tile_grammar import advance_row, initial_state
from analysis.transport.equality_band_macros import (
    EQUALITY_ROW_CHARGE,
    advance_equality_band,
    rooted_debt,
    verify_equality_band_macro,
)


class EqualityBandMacroTests(unittest.TestCase):
    def test_all_n3_corridor_triples_match_primitive_composition(self) -> None:
        accepted = rejected = 0
        for masks in product(range(1 << 3), repeat=3):
            state = initial_state(3)
            primitive_rows = []
            for mask in masks:
                outgoing = advance_row(state, mask)
                if outgoing is None:
                    break
                primitive_rows.append(tile_grammar_row_deltas(state, mask, outgoing))
                state = outgoing

            macro = advance_equality_band(initial_state(3), masks)
            if len(primitive_rows) != 3:
                rejected += 1
                self.assertIsNone(macro)
                continue

            accepted += 1
            self.assertIsNotNone(macro)
            assert macro is not None
            self.assertEqual(macro.outgoing, state)
            self.assertEqual(len(macro.structural_states), 4)
            self.assertEqual(len(macro.intermediate_states), 2)
            self.assertEqual(macro.d_u, sum(delta.u_count for delta in primitive_rows))
            self.assertEqual(macro.d_edges, sum(delta.edge_delta for delta in primitive_rows))
            self.assertEqual(macro.d_cycles, sum(delta.cycle_delta for delta in primitive_rows))
            self.assertEqual(macro.d_rank, sum(delta.rank_delta for delta in primitive_rows))
            self.assertEqual(macro.charge, 3 * EQUALITY_ROW_CHARGE)
            self.assertEqual(
                macro.weight, 3 * macro.d_u - 2 * macro.d_rank - macro.charge
            )
            self.assertEqual(macro.rooted_debt_before, rooted_debt(macro.incoming))
            self.assertEqual(macro.rooted_debt_after, rooted_debt(macro.outgoing))
            verify_equality_band_macro(macro)

        self.assertEqual(accepted + rejected, 8**3)
        self.assertGreater(accepted, 0)
        self.assertGreater(rejected, 0)

    def test_rejects_invalid_intermediate_transitions(self) -> None:
        failures = {}
        for masks in product(range(8), repeat=3):
            state = initial_state(3)
            for stage, mask in enumerate(masks, start=1):
                outgoing = advance_row(state, mask)
                if outgoing is None:
                    failures.setdefault(stage, masks)
                    break
                state = outgoing

        # At the top boundary every first row is admissible. Both later
        # primitive stages do have rejected transitions.
        self.assertEqual(set(failures), {2, 3})
        for stage, masks in failures.items():
            with self.subTest(stage=stage, masks=masks):
                self.assertIsNone(advance_equality_band(initial_state(3), masks))

    def test_rooted_debt_and_out_merge_metadata_are_exact(self) -> None:
        saw_debt = saw_out_merge = False
        for masks in product(range(8), repeat=3):
            macro = advance_equality_band(initial_state(3), masks)
            if macro is None:
                continue
            for row in macro.rows:
                self.assertEqual(
                    row.rooted_debt.delta,
                    row.rooted_debt.after - row.rooted_debt.before,
                )
                saw_debt |= row.rooted_debt.before > 0
                saw_out_merge |= bool(row.rooted_debt.incoming_blocks_merged_into_out)
        self.assertTrue(saw_debt)
        self.assertTrue(saw_out_merge)

        macro = advance_equality_band(initial_state(3), (0, 7, 3))
        self.assertIsNotNone(macro)
        assert macro is not None
        self.assertEqual(macro.rows[2].rooted_debt.before, 2)
        self.assertEqual(macro.rows[2].rooted_debt.after, 0)
        self.assertEqual(
            macro.rows[2].rooted_debt.incoming_blocks_merged_into_out, (1, 2)
        )

    def test_verifier_rejects_tampered_aggregate(self) -> None:
        macro = next(
            macro
            for masks in product(range(8), repeat=3)
            if (macro := advance_equality_band(initial_state(3), masks)) is not None
        )
        with self.assertRaisesRegex(ValueError, "totals"):
            verify_equality_band_macro(replace(macro, weight=macro.weight + 1))

    def test_invalid_shape_and_insufficient_rows(self) -> None:
        with self.assertRaisesRegex(ValueError, "exactly three"):
            advance_equality_band(initial_state(3), (0, 0))

        state = advance_row(initial_state(3), 0)
        self.assertIsNotNone(state)
        with self.assertRaisesRegex(ValueError, "below the grid"):
            advance_equality_band(state, (0, 0, 0))


if __name__ == "__main__":
    unittest.main()
