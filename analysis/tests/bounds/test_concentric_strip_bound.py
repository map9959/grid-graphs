from __future__ import annotations

import json
import os
import unittest


from analysis.bounds.concentric_strip_bound import (
    build_artifact,
    maximum_perimeter_u_edges,
    phi_three_by,
    phi_two_by,
    solve_rank_relaxation,
    solve_relaxation,
)
from analysis._paths import analysis_path
from analysis.tests._support import migrated_artifact


ARTIFACT = analysis_path("concentric_strip_bound.json")


class ConcentricStripBoundTests(unittest.TestCase):
    def test_thin_grid_formulas(self) -> None:
        self.assertEqual([phi_two_by(n) for n in range(2, 8)], [2, 3, 4, 5, 6, 7])
        self.assertEqual([phi_three_by(n) for n in range(2, 8)], [3, 4, 6, 7, 8, 10])
        self.assertEqual(maximum_perimeter_u_edges(2, 4, 4), 4)
        self.assertEqual(maximum_perimeter_u_edges(5, 4, 0), 2)
        self.assertEqual(maximum_perimeter_u_edges(5, 5, 4), 1)

    @unittest.skipUnless(os.environ.get("GRID_GRAPHS_SLOW"), "slow exact regeneration")
    def test_cached_artifact_regenerates_exactly(self) -> None:
        self.assertEqual(build_artifact(), migrated_artifact(json.loads(ARTIFACT.read_text())))

    def test_depth_three_never_weakens_the_bound(self) -> None:
        for n in range(2, 21):
            without = solve_relaxation(n, include_depth_three=False).full_total
            with_three = solve_relaxation(n, include_depth_three=True).full_total
            self.assertLessEqual(with_three, without)

    def test_known_controls_and_residue_two_gaps_are_pinned(self) -> None:
        artifact = migrated_artifact(json.loads(ARTIFACT.read_text()))
        table = {item["n"]: item for item in artifact["table"]}
        self.assertEqual(table[4]["degree_plus_depth_two_three_bound"], 8)
        self.assertEqual(
            [
                (item["n"], item["relaxation_upper_bound_P"], item["gap_above_proposed_formula"])
                for item in artifact["residue_two"]
            ],
            [(5, 13, 2), (8, 30, 3), (11, 53, 4), (14, 82, 5), (17, 117, 7), (20, 158, 8)],
        )
        self.assertEqual(
            [item["rank_aware_upper_bound_P"] for item in artifact["residue_two"]],
            [12, 30, 53, 82, 117, 158],
        )

    def test_rank_aware_relaxation_is_never_weaker(self) -> None:
        artifact = migrated_artifact(json.loads(ARTIFACT.read_text()))
        for item in artifact["residue_two"]:
            self.assertLessEqual(
                item["rank_aware_upper_bound_P"], item["relaxation_upper_bound_P"]
            )
        self.assertLessEqual(
            solve_rank_relaxation(5, include_depth_three=False).full_total,
            solve_relaxation(5).full_total,
        )

    def test_exact_small_anchors_are_never_weaker(self) -> None:
        artifact = migrated_artifact(json.loads(ARTIFACT.read_text()))
        for n in range(2, 21):
            scalar = solve_relaxation(n).full_total
            anchored = solve_relaxation(n, use_exact_small_anchors=True).full_total
            self.assertLessEqual(anchored, scalar)
        self.assertEqual(
            [item["n"] for item in artifact["table"] if item["depth_three_improvement"]],
            [6, 9],
        )


if __name__ == "__main__":
    unittest.main()
