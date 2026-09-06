from __future__ import annotations

import json
import unittest

from analysis._paths import analysis_path
from analysis.bounds.concentric_connectivity_profile import (
    build_artifact,
    port_word_signature,
)
from analysis.tests._support import migrated_artifact

ARTIFACT = analysis_path("concentric_connectivity_profile.json")


class ConcentricConnectivityProfileTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.artifact = migrated_artifact(json.loads(ARTIFACT.read_text()))

    def test_cached_artifact_regenerates_exactly(self) -> None:
        self.assertEqual(build_artifact(), self.artifact)

    def test_port_word_signature_forgets_only_singleton_names(self) -> None:
        signature = port_word_signature((4, 7, 4, 9, 7, 11))
        self.assertEqual(signature.repeated_components, 2)
        self.assertEqual(signature.tokens, ("R0", "R1", "R0", "S", "R1", "S"))

    def test_known_witness_rank_profiles(self) -> None:
        expected = {
            "n5-exact": (14, 16, 17, 0),
            "n8-exact": (37, 49, 50, 0),
            "n11-exact": (72, 101, 101, 1),
            "n14-exact": (119, 170, 170, 1),
            "n17-affine": (179, 257, 257, 1),
            "n20-phase": (250, 362, 362, 1),
        }
        actual = {
            name: (item["u_count"], item["dual_edges"], item["dual_vertices"], item["cycle_rank"])
            for name, item in self.artifact["witnesses"].items()
        }
        self.assertEqual(actual, expected)
        self.assertTrue(
            all(
                item["outward_annuli"]["all_stages_unsealed"]
                for item in self.artifact["witnesses"].values()
            )
        )
        self.assertEqual(
            self.artifact["observed_feasible_port_signature_bounds"],
            {
                "maximum_repeated_components": 4,
                "maximum_cyclic_runs_per_component": 3,
                "maximum_compressed_runs": 9,
                "scope": "known feasible witnesses n=5,8,11,14,17,20 only",
            },
        )

    def test_n5_scalar_optimum_has_rank_deficit_two(self) -> None:
        census = self.artifact["n5_scalar_maximum_census"]
        self.assertEqual(census["patterns"], 1820)
        self.assertEqual(census["connected_patterns"], 0)
        self.assertEqual(census["maximum_rank"], 14)
        self.assertEqual(census["required_rank"], 16)
        self.assertEqual(census["minimum_component_count"], 3)

    def test_n8_scalar_controls_expose_two_distinct_rank_failures(self) -> None:
        controls = self.artifact["scalar_optimum_controls"]["n8-scalar-optimum"]
        edge = controls["maximum_edge_pattern"]
        rank = controls["rank_maximizing_pattern"]
        self.assertEqual((edge["graphic_rank"], edge["cycle_rank"], edge["components"]), (42, 7, 8))
        self.assertEqual((rank["graphic_rank"], rank["cycle_rank"], rank["components"]), (45, 0, 5))
        self.assertEqual(edge["centered_prefixes"][-1]["sealed_components"], 7)
        self.assertEqual(rank["centered_prefixes"][-1]["sealed_components"], 4)

    def test_complete_small_equality_controls_are_included(self) -> None:
        controls = self.artifact["complete_small_equality_controls"]
        self.assertEqual(controls["n5-complete-equality"]["distinct_patterns"], 242)
        self.assertEqual(controls["n8-complete-equality"]["distinct_patterns"], 704)
        self.assertEqual(controls["n5-complete-equality"]["violating_patterns"], 0)
        self.assertEqual(controls["n8-complete-equality"]["violating_patterns"], 0)


if __name__ == "__main__":
    unittest.main()
