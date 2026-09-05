from __future__ import annotations

import random
import unittest

from cotree_row_charge import (
    extend_forced_set_to_tree,
    profile,
    random_spanning_tree,
    spanning_trees,
)


class CotreeRowChargeTests(unittest.TestCase):
    def test_exact_ledgers_and_ocb_on_all_three_by_three_trees(self) -> None:
        items = [profile(3, tree) for tree in spanning_trees(3)]
        self.assertEqual(len(items), 192)
        self.assertGreaterEqual(min(item.ocb_slack for item in items), 0)

    def test_row_local_root_allocation_is_false(self) -> None:
        # OCB may hold even though w_r >= 1 + roots_r does not hold linewise.
        values = [
            line.waste - line.component_roots - 1
            for tree in spanning_trees(3)
            for lines in (profile(3, tree).rows, profile(3, tree).columns)
            for line in lines
        ]
        self.assertLess(min(values), 0)

    def test_wilson_samples_are_trees_and_satisfy_exact_ledgers(self) -> None:
        rng = random.Random(17)
        for n in (4, 7):
            for _ in range(10):
                item = profile(n, random_spanning_tree(n, rng))
                self.assertGreaterEqual(item.ocb_slack, 0)

    def test_extend_maximum_three_by_three_forced_witness(self) -> None:
        # One of the maximum forced sets: F is encoded in little-endian rows.
        item = profile(3, extend_forced_set_to_tree(3, (1, 0, 7)))
        self.assertEqual(item.waste, 7)
        self.assertGreaterEqual(item.ocb_slack, 0)


if __name__ == "__main__":
    unittest.main()
