from __future__ import annotations

import json
import unittest


from analysis.patterns.diagonal_patterns import residue_two_affine_pattern
from analysis.residue_certificates.residue_two_affine_motif_grammar import replay_trace
from analysis.residue_certificates.residue_two_compact_transition import (
    AFFINE_WIDTHS,
    ActionKey,
    build_artifact,
    control_key,
    encode_compact_boundary_defect_frontier,
    endpoint_tag,
    observe_transition,
    size_regime,
)
from analysis._paths import analysis_path
from analysis.tests._support import migrated_artifact


ARTIFACT = analysis_path("residue_two_compact_transition.json")


class ResidueTwoCompactTransitionTests(unittest.TestCase):
    def test_endpoint_tags_are_width_relative(self) -> None:
        self.assertEqual(
            [endpoint_tag(index, 9) for index in (0, 1, 5, 6, 7, 8)],
            ["L0", "L1", "R3", "R2", "R1", "R0"],
        )
        with self.assertRaisesRegex(ValueError, "allowed endpoint"):
            endpoint_tag(3, 9)
        self.assertEqual(
            [size_regime(length) for length in (3, 4, 5, 6, 7, 20)],
            ["small", "small", "base17", "base20", "stable", "stable"],
        )

    def test_one_edge_round_trips_and_uses_normalized_keys(self) -> None:
        rows = residue_two_affine_pattern(17)
        states = replay_trace(rows)
        edge = observe_transition(states[8], rows[8], states[9])
        self.assertIsInstance(edge.action, ActionKey)
        self.assertEqual(edge.deltas.row, 1)
        self.assertEqual(edge.deltas.length, 0)
        source = control_key(encode_compact_boundary_defect_frontier(states[8]))
        self.assertEqual(edge.source, source)
        self.assertNotIn("row_index", source.__dataclass_fields__)
        self.assertNotIn("u_cost", source.__dataclass_fields__)
        self.assertNotIn("length", source.__dataclass_fields__)

    def test_cached_artifact_reports_finite_determinism_census(self) -> None:
        artifact = migrated_artifact(json.loads(ARTIFACT.read_text()))
        self.assertEqual(artifact["scope"]["affine_generated_widths"], list(AFFINE_WIDTHS))
        self.assertFalse(artifact["scope"]["arbitrary_k_proof"])
        census = artifact["census"]
        self.assertEqual(census["transitions"], sum(AFFINE_WIDTHS))
        self.assertTrue(census["deterministic"])
        self.assertEqual(census["conflicting_source_action_pairs"], 0)
        self.assertEqual(census["determinism_conflict_witnesses"], [])
        self.assertEqual(len(artifact["transition_ledger"]), census["transitions"])
        self.assertEqual(len(artifact["rule_catalog"]), census["distinct_rules"])
        self.assertFalse(
            artifact["stabilization"]["stabilization_beyond_observed_range_claimed"]
        )
        for width in ("11", "14"):
            coverage = artifact["fixed_equality_coverage"][width]
            self.assertEqual(len(coverage["transition_coverage"]), int(width))
        self.assertTrue(artifact["verification"]["all_checks_passed"])

    def test_cached_artifact_regenerates_exactly(self) -> None:
        self.assertEqual(build_artifact(), migrated_artifact(json.loads(ARTIFACT.read_text())))


if __name__ == "__main__":
    unittest.main()
