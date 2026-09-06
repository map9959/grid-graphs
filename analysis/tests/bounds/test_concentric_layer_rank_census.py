from __future__ import annotations

import json
import unittest

from analysis._paths import analysis_path
from analysis.bounds.proof_oriented_identities import check_pattern_identities
from analysis.tests._support import migrated_artifact

ARTIFACT = analysis_path("concentric_layer_rank_census.json")


class ConcentricLayerRankCensusTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.artifact = migrated_artifact(json.loads(ARTIFACT.read_text()))

    def test_exact_census_counts_and_rank_deficits(self) -> None:
        n5 = self.artifact["cases"]["n5-scalar-optimum"]
        n8 = self.artifact["cases"]["n8-scalar-optimum"]
        self.assertEqual(
            (n5["patterns"], n5["maximum_rank"], n5["required_rank"]),
            (1820, 14, 16),
        )
        self.assertEqual(
            (n8["patterns"], n8["maximum_rank"], n8["required_rank"]),
            (4462920, 45, 49),
        )
        self.assertEqual(n8["maximum_dual_edges"], 49)
        self.assertEqual(n8["maximum_rank_at_maximum_edges"], 42)
        self.assertEqual(n8["minimum_cycles_at_maximum_edges"], 7)
        self.assertEqual(n8["connected_patterns"], 0)

    def test_committed_patterns_replay_exactly(self) -> None:
        for item in self.artifact["cases"].values():
            ranked = check_pattern_identities(item["rank_maximizing_pattern"])
            edged = check_pattern_identities(item["maximum_edge_pattern"])
            self.assertEqual(ranked.graphic_rank, item["maximum_rank"])
            self.assertEqual(edged.dual_edges, item["maximum_dual_edges"])


if __name__ == "__main__":
    unittest.main()
