from __future__ import annotations

import json
import os
import unittest

from analysis._paths import analysis_path
from analysis.tests._support import migrated_artifact
from analysis.transport.equality_moving_slab import build_census


class EqualityMovingSlabTests(unittest.TestCase):
    def test_cached_census_records_acyclic_cycle_preserving_transport(self) -> None:
        artifact = migrated_artifact(json.loads(
            analysis_path("equality_moving_slab.json").read_text()
        ))
        census = artifact["census"]
        self.assertEqual(census["source_paths"], 242)
        self.assertEqual(census["target_paths"], 704)
        self.assertEqual(census["successful_target_paths"], 58)
        self.assertEqual(census["alignment_paths"], 3_517)
        self.assertEqual(census["terminal_cycle_preserving_alignments"], 1_849)
        self.assertEqual(
            census["terminal_cycle_delta_histogram"],
            {"-2": 36, "-1": 258, "0": 1_849, "1": 652, "2": 251, "3": 471},
        )
        self.assertEqual(
            census["cycle_preserving_interior_decoration_graph"],
            {
                "vertices": 96,
                "edges": 159,
                "self_loops": 0,
                "vertices_on_directed_cycles": 0,
            },
        )

    @unittest.skipUnless(os.environ.get("GRID_GRAPHS_SLOW"), "slow moving-slab census")
    def test_cached_census_regenerates_exactly(self) -> None:
        artifact = migrated_artifact(json.loads(
            analysis_path("equality_moving_slab.json").read_text()
        ))
        self.assertEqual(build_census(), artifact)


if __name__ == "__main__":
    unittest.main()
