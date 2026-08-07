from __future__ import annotations

import json
import unittest
from pathlib import Path

from concentric_equality_census import BOUNDS, build_artifact


ARTIFACT = Path(__file__).with_name("concentric_equality_census.json")


class ConcentricEqualityCensusTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.artifact = json.loads(ARTIFACT.read_text())

    def test_complete_small_equality_classes(self) -> None:
        n5 = self.artifact["cases"]["n5-complete-equality"]
        n8 = self.artifact["cases"]["n8-complete-equality"]
        self.assertEqual((n5["minimum_u"], n5["distinct_patterns"]), (14, 242))
        self.assertEqual((n8["minimum_u"], n8["distinct_patterns"]), (37, 704))
        self.assertEqual(n5["minimum_path_count"], n5["distinct_patterns"])
        self.assertEqual(n8["minimum_path_count"], n8["distinct_patterns"])

    def test_declared_bounds_survive_complete_census(self) -> None:
        for case in self.artifact["cases"].values():
            self.assertEqual(case["violating_patterns"], 0)
            self.assertIsNone(case["first_violation"])
            for field, bound in BOUNDS.items():
                self.assertLessEqual(case["maxima"][field], bound)

    def test_cached_artifact_regenerates_exactly(self) -> None:
        self.assertEqual(build_artifact(), self.artifact)


if __name__ == "__main__":
    unittest.main()
