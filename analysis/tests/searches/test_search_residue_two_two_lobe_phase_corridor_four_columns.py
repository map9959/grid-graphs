from __future__ import annotations

import json
import unittest
from math import comb

from analysis.searches.search_residue_two_middle import KNOWN_249_NEAR
from analysis.searches.search_residue_two_two_lobe_phase_corridor import (
    CAP_DISTRIBUTIONS,
    masks_with_u_count,
)
from analysis.searches.search_residue_two_two_lobe_phase_corridor_four_columns import (
    DEFAULT_RESULT,
    FIXED_BODY_ROWS,
    FROZEN_PACKET_COLUMNS,
    MUTABLE_PACKET_COLUMNS,
    MUTABLE_ROWS,
    body_search,
    frontier_sha256,
    mutable_row_words,
    phase_rows,
    provenance,
    row_domains,
    scope,
    validate_scope,
)
from analysis.tests._support import migrated_artifact, slow_test


class FourColumnTwoLobePhaseCorridorTests(unittest.TestCase):
    def test_exact_widened_scope_and_complete_row_domains(self) -> None:
        rows = phase_rows()
        validate_scope(rows)
        domains = row_domains(rows)
        self.assertEqual(MUTABLE_ROWS, (4, 5, 6, 7, 8, 9, 14, 15, 16, 17))
        self.assertEqual(FIXED_BODY_ROWS, (0, 1, 2, 3, 10, 11, 12, 13))
        self.assertEqual(MUTABLE_PACKET_COLUMNS, (0, 1, 2, 3))
        self.assertEqual(FROZEN_PACKET_COLUMNS, (4, 5))
        self.assertEqual([len(domains[row]) for row in MUTABLE_ROWS], [31] + [52] * 9)
        for row in MUTABLE_ROWS:
            self.assertIn(rows[row], domains[row])
            self.assertIn(KNOWN_249_NEAR[row], domains[row])
            frozen = mutable_row_words(rows, row)[0][4:]
            self.assertTrue(all(word[4:] == frozen for word in mutable_row_words(rows, row)))

    def test_exact_cap_mask_counts(self) -> None:
        self.assertEqual(CAP_DISTRIBUTIONS, ((19, 1), (18, 2), (17, 3)))
        for first, second in CAP_DISTRIBUTIONS:
            self.assertEqual(len(masks_with_u_count(first)), comb(20, first))
            self.assertEqual(len(masks_with_u_count(second)), comb(20, second))

    def test_committed_result_is_valid(self) -> None:
        record = migrated_artifact(json.loads(DEFAULT_RESULT.read_text()))
        rows = phase_rows()
        self.assertEqual(record["provenance"], provenance(rows))
        self.assertEqual(record["scope"], scope(rows))
        self.assertTrue(record["exact"])
        self.assertEqual(record["result"], "negative")
        self.assertEqual(record["fixed_cap"]["result"], "negative")
        self.assertTrue(all(item["result"] == "negative" for item in record["cap_distributions"]))

    @slow_test
    def test_committed_result_matches_exact_widened_frontier(self) -> None:
        record = migrated_artifact(json.loads(DEFAULT_RESULT.read_text()))
        rows = phase_rows()
        layer, stats = body_search(rows, report=False)
        self.assertEqual(len(record["completed_body_rows"]), len(stats))
        self.assertEqual(record["corridor_after_row17"]["states"], len(layer))
        self.assertEqual(
            record["corridor_after_row17"]["assignments_represented"],
            sum(node.ways for node in layer.values()),
        )
        self.assertEqual(
            record["corridor_after_row17"]["frontier_sha256"], frontier_sha256(layer)
        )
        self.assertEqual(
            [item["distribution"] for item in record["cap_distributions"]],
            [[19, 1], [18, 2], [17, 3]],
        )
        self.assertEqual(
            [[row["mask_count"] for row in item["rows"]] for item in record["cap_distributions"]],
            [[20, 20], [190, 190], [1140, 1140]],
        )


if __name__ == "__main__":
    unittest.main()
