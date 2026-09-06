from __future__ import annotations

import itertools
import json
import unittest

from analysis._paths import analysis_path
from analysis.residue_geometry.classify_residue_two_staircase_seam import (
    build_report,
    cap_maximum,
    forced_forest,
    packet_paths,
    seam_core,
    transition_valid,
)
from analysis.tests._support import migrated_artifact

ARTIFACT = analysis_path("residue_two_staircase_seam.json")


class ResidueTwoStaircaseSeamTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.report = build_report()

    def test_three_step_transfer_grammar(self) -> None:
        self.assertTrue(transition_valid(0, 1, 1, 0, 0))
        self.assertEqual(packet_paths(0, 0), [
            (1, (0, 0, 3)), (1, (0, 1, 2)), (1, (0, 2, 1)),
            (1, (0, 3, 0)), (1, (1, 0, 2)), (1, (1, 1, 1)),
            (1, (1, 2, 0)), (2, (0, 0, 3)), (2, (0, 1, 2)),
            (2, (0, 2, 1)), (2, (0, 3, 0)),
        ])
        self.assertEqual(self.report["seam_automaton"]["local_packet_paths"], 99)

    def test_uniform_diagonal_seam_count(self) -> None:
        self.assertEqual(
            [len(seam_core(k, 0, 0, 1, (1, 1, 1))) - 3 * k * k for k in (7, 8, 9)],
            [13, 15, 17],
        )

    def test_cap_automaton_matches_exhaustive_toy_ring(self) -> None:
        k = 1
        n = 3 * k + 2
        core = seam_core(k, 0, 0, 1, (1, 1, 1))
        perimeter = [
            (row, column)
            for row in range(n)
            for column in range(n)
            if row in (0, n - 1) or column in (0, n - 1)
        ]
        brute = max(
            sum(word)
            for word in itertools.product((0, 1), repeat=len(perimeter))
            if forced_forest(
                n,
                core | {vertex for vertex, occupied in zip(perimeter, word, strict=True) if occupied},
            )
        )
        self.assertEqual(cap_maximum(k, core)["maximum"], brute)

    def test_complete_cap_obstruction(self) -> None:
        self.assertEqual(self.report["status"], "staircase_seam_obstructed")
        self.assertFalse(self.report["target"]["attainable"])
        self.assertEqual(self.report["target"]["surviving_paths"], 0)
        self.assertTrue(all(self.report["checks"].values()))

    def test_best_formulas_and_k_7_8_9_caps(self) -> None:
        best = self.report["best_path"]
        self.assertEqual(best["formulas"]["total"], "3k^2 + 6k + 2")
        self.assertEqual([record["total"] for record in best["records"]], [191, 242, 299])
        self.assertEqual([record["cap"]["maximum"] for record in best["records"]], [57, 65, 73])
        self.assertEqual(
            self.report["cycle_classification"]["capacity_certificate"]["observed_successor_gains_k7_and_k8"],
            [51, 57],
        )

    def test_artifact_is_current(self) -> None:
        self.assertEqual(migrated_artifact(json.loads(ARTIFACT.read_text())), self.report)


if __name__ == "__main__":
    unittest.main()
