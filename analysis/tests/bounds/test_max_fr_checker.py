from __future__ import annotations

import itertools
import unittest

from analysis.bounds.forced_forest_row_grammar import is_forced_forest
from analysis.bounds.max_fr_checker import (
    CORNERS,
    check_max_fr,
    crop_rows,
    maximum_repair_rank,
    summarize_results,
    transform,
)


def direct_repair_rank(mandatory: tuple[int, ...]) -> int:
    m = len(mandatory)
    best = 0
    optional = [(r, c) for r in range(m) for c in range(m) if not mandatory[r] >> c & 1]
    for choices in itertools.product((False, True), repeat=len(optional)):
        rows = list(mandatory)
        for selected, (r, c) in zip(choices, optional):
            if selected:
                rows[r] |= 1 << c
        if is_forced_forest(m, rows):
            best = max(best, sum(choices))
    return best


class MaxFRCheckerTests(unittest.TestCase):
    def test_crop_offsets_match_four_corner_embeddings(self) -> None:
        rows = tuple(1 << r for r in range(6))
        self.assertEqual(crop_rows(6, rows, "NW"), (1, 2, 4))
        self.assertEqual(crop_rows(6, rows, "NE"), (0, 0, 0))
        self.assertEqual(crop_rows(6, rows, "SW"), (0, 0, 0))
        self.assertEqual(crop_rows(6, rows, "SE"), (1, 2, 4))

    def test_exact_repair_dp_matches_all_small_crops(self) -> None:
        for m in range(1, 4):
            row_mask = (1 << m) - 1
            for encoded in range(1 << (m * m)):
                mandatory = tuple((encoded >> (m * r)) & row_mask for r in range(m))
                if is_forced_forest(m, list(mandatory)):
                    self.assertEqual(maximum_repair_rank(mandatory), direct_repair_rank(mandatory))

    def test_checker_frame_loss_and_signed_sum(self) -> None:
        rows = (1, 0, 0, 0)
        result = check_max_fr(4, rows)
        self.assertEqual([item.corner for item in result.corners], list(CORNERS))
        self.assertEqual([item.loss for item in result.corners], [0, 1, 1, 1])
        self.assertEqual(result.signed_rhs, sum(item.loss - 8 for item in result.corners))
        self.assertEqual(result.min_corner_frame_loss, 0)
        self.assertEqual(result.min_loss_minus_2n, -8)
        self.assertEqual(result.minimum_repair_rank_needed, 0)
        self.assertTrue(result.minimum_loss_crop_balanced)
        self.assertTrue(result.max_fr)
        self.assertTrue(result.some_crop_balanced)

    def test_dihedral_transform_preserves_cardinality_and_acyclicity(self) -> None:
        rows = (0b000, 0b010, 0b000)
        for rotation in range(4):
            for reflect in (False, True):
                image = transform(rows, rotation, reflect)
                self.assertEqual(sum(map(int.bit_count, image)), 1)
                self.assertTrue(is_forced_forest(3, list(image)))

    def test_nine_counterexample_and_rank_one_replay(self) -> None:
        rows = (509, 1, 65, 285, 257, 353, 265, 257, 381)
        self.assertTrue(is_forced_forest(9, list(rows)))
        self.assertEqual(sum(mask.bit_count() for mask in rows), 34)
        result = check_max_fr(9, rows)
        self.assertEqual([item.loss for item in result.corners], [20, 20, 19, 19])
        self.assertEqual([item.repair_rank for item in result.corners], [1, 1, 1, 1])
        self.assertEqual((result.rank_sum, result.signed_rhs), (4, 6))
        self.assertEqual(result.min_corner_frame_loss, 19)
        self.assertEqual(result.min_loss_minus_2n, 1)
        self.assertEqual(result.minimum_repair_rank_needed, 1)
        self.assertTrue(result.minimum_loss_crop_balanced)
        self.assertFalse(result.max_fr)
        self.assertTrue(result.some_crop_balanced)

        # Independent rank-one upper replay: every pair of eligible repairs
        # makes the directly constructed repaired forced graph cyclic.
        for corner in CORNERS:
            mandatory = crop_rows(9, rows, corner)
            eligible = [
                (r, c)
                for r in range(6)
                for c in range(6)
                if not mandatory[r] >> c & 1
            ]
            self.assertTrue(
                any(
                    is_forced_forest(
                        6, [mask | ((r == rr) << c) for rr, mask in enumerate(mandatory)]
                    )
                    for r, c in eligible
                )
            )
            for (r1, c1), (r2, c2) in itertools.combinations(eligible, 2):
                repaired = list(mandatory)
                repaired[r1] |= 1 << c1
                repaired[r2] |= 1 << c2
                self.assertFalse(is_forced_forest(6, repaired))

    def test_nine_balanced_crop_counterexample_and_rank_zero_replay(self) -> None:
        rows = (509, 1, 65, 285, 257, 369, 261, 1, 505)
        self.assertTrue(is_forced_forest(9, list(rows)))
        self.assertEqual(sum(mask.bit_count() for mask in rows), 34)
        result = check_max_fr(9, rows)
        self.assertEqual([item.loss for item in result.corners], [19, 19, 19, 19])
        self.assertEqual([item.demand for item in result.corners], [1, 1, 1, 1])
        self.assertEqual([item.repair_rank for item in result.corners], [0, 0, 0, 0])
        self.assertEqual(result.min_loss_minus_2n, 1)
        self.assertEqual(result.minimum_repair_rank_needed, 1)
        self.assertFalse(result.minimum_loss_crop_balanced)
        self.assertFalse(result.some_crop_balanced)

        # Rank zero is independently visible: every eligible singleton repair
        # makes the directly constructed crop forced graph cyclic.
        for corner in CORNERS:
            mandatory = crop_rows(9, rows, corner)
            for r in range(6):
                for c in range(6):
                    if mandatory[r] >> c & 1:
                        continue
                    repaired = list(mandatory)
                    repaired[r] |= 1 << c
                    self.assertFalse(is_forced_forest(6, repaired))

    def test_summary_distinguishes_max_fr_from_balanced_crop(self) -> None:
        max_fr_only = check_max_fr(9, (509, 1, 65, 285, 257, 353, 265, 257, 381))
        no_balanced_crop = check_max_fr(9, (509, 1, 65, 285, 257, 369, 261, 1, 505))
        summary = summarize_results(9, "regression", [max_fr_only, no_balanced_crop])
        self.assertFalse(summary["max_fr"])
        self.assertFalse(summary["some_crop_balanced"])
        self.assertEqual(
            summary["some_crop_balanced_distribution"], {"false": 1, "true": 1}
        )


if __name__ == "__main__":
    unittest.main()
