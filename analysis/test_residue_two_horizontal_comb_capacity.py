from __future__ import annotations

import json
from pathlib import Path
import unittest

from residue_two_horizontal_comb_capacity import build_report


ARTIFACT = Path(__file__).with_name("residue_two_horizontal_comb_capacity.json")


class ResidueTwoHorizontalCombCapacityTests(unittest.TestCase):
    def test_local_unit_cell_capacity(self) -> None:
        report = build_report()
        self.assertEqual(
            [item["best_net_gain"] for item in report["local_census"]["connectors"]],
            [-1, -2],
        )
        self.assertTrue(report["checks"]["all_local_caps_nonpositive"])

    def test_k_7_8_9_are_disjoint_forced_forests_below_target(self) -> None:
        report = build_report()
        self.assertEqual(report["status"], "proved_capacity_obstruction")
        self.assertEqual(
            [record["capacity_deficit"] for record in report["records"]],
            [12, 14, 16],
        )
        self.assertTrue(report["checks"]["all_deterministic_instances_pass"])

    def test_checked_artifact_is_current(self) -> None:
        self.assertEqual(json.loads(ARTIFACT.read_text()), build_report())


if __name__ == "__main__":
    unittest.main()
