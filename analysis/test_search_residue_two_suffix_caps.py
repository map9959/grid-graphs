from __future__ import annotations

import json
import unittest
from math import comb

from search_residue_two_suffix_caps import (
    DISTRIBUTIONS,
    DEFAULT_CERTIFICATE,
    N,
    certificate,
    masks_with_u_count,
    search,
)
from search_residue_two_suffix_corridor import layer_after_row17
from test_support import slow_test


class SuffixCapsTests(unittest.TestCase):
    def test_mask_languages_are_complete_and_unique(self) -> None:
        for row18_u, row19_u in DISTRIBUTIONS:
            for count in (row18_u, row19_u):
                masks = masks_with_u_count(count)
                self.assertEqual(len(masks), comb(N, count))
                self.assertEqual(len(set(masks)), len(masks))
                self.assertTrue(all(mask.bit_count() == count for mask in masks))

    def test_committed_certificate_is_valid(self) -> None:
        committed = json.loads(DEFAULT_CERTIFICATE.read_text())
        self.assertTrue(committed["exact"])
        self.assertEqual(committed["result"], "negative")
        self.assertEqual(committed["corridor_after_row17"]["exact_states"], 2)
        self.assertIsNone(committed["witness"])

    @slow_test
    def test_corridor_layer_is_exact_cost_229(self) -> None:
        layer, _ = layer_after_row17(report=False)
        self.assertEqual(len(layer), 2)
        self.assertEqual(sum(node.ways for node in layer.values()), 3)
        self.assertTrue(all(state.row_index == 18 and state.u_cost == 229 for state in layer))

    @slow_test
    def test_full_exact_cap_search(self) -> None:
        result = search(report=False)
        self.assertIsNone(result.witness)
        self.assertEqual(result.corridor_exact_states, 2)
        self.assertEqual(result.corridor_assignment_multiplicity, 3)
        self.assertEqual(
            [
                (
                    stats.row18_masks_attempted,
                    stats.row18_transitions_attempted,
                    stats.row18_live,
                    stats.row18_exact_states,
                    stats.row18_assignment_multiplicity,
                    stats.row19_pairs_attempted,
                    stats.row19_pairs_live,
                    stats.row19_pairs_accepted,
                    stats.row19_exact_states,
                    stats.row19_live_assignment_multiplicity,
                    stats.accepted_assignment_multiplicity,
                )
                for stats in result.distributions
            ],
            [
                (20, 40, 16, 16, 24, 320, 0, 0, 0, 0, 0),
                (190, 380, 52, 52, 78, 9_880, 0, 0, 0, 0, 0),
                (1_140, 2_280, 90, 90, 135, 102_600, 0, 0, 0, 0, 0),
            ],
        )
        scope = certificate(result)["scope"]
        self.assertIsNone(scope["beam"])
        self.assertIsNone(scope["state_cap"])
        self.assertIsNone(scope["partition_projection"])

    @slow_test
    def test_committed_certificate_matches_fresh_exact_result(self) -> None:
        result = search(report=False)
        committed = json.loads(DEFAULT_CERTIFICATE.read_text())
        self.assertEqual(committed, certificate(result))


if __name__ == "__main__":
    unittest.main()
