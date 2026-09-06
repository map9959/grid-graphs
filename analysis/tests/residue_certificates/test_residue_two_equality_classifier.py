from __future__ import annotations

import json
import os
import unittest

from analysis._paths import analysis_path
from analysis.patterns.diagonal_patterns import (
    residue_two_affine_pattern,
    residue_two_explicit_pattern,
)
from analysis.residue_certificates.residue_two_equality_classifier import (
    RootedDebt,
    build_artifact,
    canonical_rooted_partition,
    classify_masks,
)
from analysis.tests._support import migrated_artifact
from analysis.tiles.tile_grammar import FrontierState, row_mask

ARTIFACT = analysis_path("residue_two_equality_classifier.json")


class ResidueTwoEqualityClassifierTests(unittest.TestCase):
    def test_rooted_partition_and_debt_bits_are_explicit(self) -> None:
        self.assertEqual(canonical_rooted_partition((7, 9, 7, 4)), (0, 1, 0, 2))
        state = FrontierState(4, 2, 0b0110, (7, 9, 7, 4), 4, 2)
        debt = RootedDebt.from_state(state)
        self.assertEqual(debt.boundary_mode, "open")
        self.assertEqual(debt.out_coverage_bits, (1, 0, 0, 0))
        self.assertEqual(debt.closure_bits, (1, 1, 0))
        self.assertEqual(debt.unresolved_components, 2)
        self.assertEqual(debt.attachment_debt, 2)
        self.assertEqual(debt.decorated_debt, 4)

    def test_fixed_witness_path_weight_controls(self) -> None:
        for n, rows, expected in (
            (11, residue_two_explicit_pattern(11), 5),
            (14, residue_two_explicit_pattern(14), 5),
            (17, residue_two_affine_pattern(17), 8),
        ):
            with self.subTest(n=n):
                classes, transitions, total = classify_masks(tuple(map(row_mask, rows)))
                self.assertEqual(total, expected)
                self.assertEqual(len(classes), n + 1)
                self.assertEqual(len(transitions), n)
                self.assertEqual(classes[-1].closure_bits, (0, 0, 1))
        self.assertEqual(sum(row.count("U") for row in residue_two_affine_pattern(17)), 179)

    def test_cached_artifact_records_scope_counts_and_controls(self) -> None:
        artifact = migrated_artifact(json.loads(ARTIFACT.read_text()))
        self.assertEqual(artifact["scope"]["semantics"], "finite-width-enumerated-path-diagnostic-only")
        self.assertFalse(artifact["scope"]["coverage_beyond_enumerated_paths_claimed"])
        self.assertFalse(artifact["scope"]["theorem_or_certificate"])
        self.assertEqual(artifact["sources"]["n5-exact-corridor"]["path_total_weights"], {"5": 242})
        self.assertEqual(artifact["sources"]["n8-exact-corridor"]["path_total_weights"], {"5": 704})
        self.assertEqual(artifact["sources"]["n11-fixed-witness"]["path_total_weights"], {"5": 1})
        self.assertEqual(artifact["sources"]["n14-fixed-witness"]["path_total_weights"], {"5": 1})
        self.assertEqual(artifact["sources"]["n17-fixed-witness"]["path_total_weights"], {"8": 1})
        self.assertIn("strong_components", artifact["quotient_graph"])

    @unittest.skipUnless(os.environ.get("GRID_GRAPHS_SLOW"), "slow exact regeneration")
    def test_cached_artifact_regenerates_exactly(self) -> None:
        self.assertEqual(build_artifact(), migrated_artifact(json.loads(ARTIFACT.read_text())))


if __name__ == "__main__":
    unittest.main()
