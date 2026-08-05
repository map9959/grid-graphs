from __future__ import annotations

import json
import os
import unittest
from pathlib import Path

from residue_two_equality_cegar import (
    LEVELS,
    abstract_key,
    build_artifact,
    observe_corridor,
)
from equality_corridor import build_equality_corridor


ARTIFACT = Path(__file__).with_name("residue_two_equality_cegar.json")


class ResidueTwoEqualityCegarTests(unittest.TestCase):
    def test_hierarchy_refines_and_exact_key_is_structural_control(self) -> None:
        observations = observe_corridor(build_equality_corridor(5))
        for observed in observations:
            coarse = abstract_key(observed.state, "coarse")
            attachment = abstract_key(observed.state, "attachment")
            exact = abstract_key(observed.state, "exact")
            self.assertEqual(attachment[:-1], coarse)
            self.assertEqual(exact[0], 5)
        with self.assertRaises(ValueError):
            abstract_key(observations[0].state, "unknown")

    def test_complete_width_five_observation_uses_all_corridor_edges(self) -> None:
        corridor = build_equality_corridor(5)
        observations = observe_corridor(corridor)
        self.assertEqual(len(observations), 117)
        self.assertEqual(sum(map(len, corridor.corridor_edges)), 220)
        initial = next(item for item in observations if item.state.row_index == 0)
        # Distinct concrete paths may have the same normalized behavior word.
        self.assertEqual(len(initial.accepting_suffixes), 236)
        self.assertTrue(all(len(word) == 5 for word in initial.accepting_suffixes))

    def test_cached_artifact_records_complete_scope_and_collision_kinds(self) -> None:
        artifact = json.loads(ARTIFACT.read_text())
        self.assertEqual(artifact["definitions"]["hierarchy"], list(LEVELS))
        self.assertEqual(artifact["corridors"]["5"]["minimum_path_count"], "242")
        self.assertEqual(artifact["corridors"]["8"]["minimum_path_count"], "704")
        self.assertEqual(artifact["observations"]["states"], 325)
        self.assertEqual(artifact["observations"]["outgoing_equality_transitions"], 588)
        expected = {
            "coarse": (193, 80, 51, 24, 33),
            "attachment": (227, 72, 37, 1, 36),
            "exact": (325, 0, 0, 0, 0),
        }
        fields = (
            "keys",
            "merged_groups",
            "collision_groups",
            "cross_width_collision_groups",
            "within_width_collision_groups",
        )
        for level, counts in expected.items():
            self.assertEqual(
                tuple(artifact["hierarchy"][level][field] for field in fields), counts
            )
        self.assertEqual(
            artifact["hierarchy"]["attachment"]["bulk_cross_width_collision_groups"],
            0,
        )
        for level in ("coarse", "attachment"):
            for collision in artifact["hierarchy"][level]["collisions"]:
                self.assertTrue(
                    collision["cross_width_witness"] is not None
                    or collision["within_width_witness"] is not None
                )

    @unittest.skipUnless(os.environ.get("GRID_GRAPHS_SLOW"), "slow exact regeneration")
    def test_cached_artifact_regenerates_exactly(self) -> None:
        self.assertEqual(build_artifact(), json.loads(ARTIFACT.read_text()))


if __name__ == "__main__":
    unittest.main()
