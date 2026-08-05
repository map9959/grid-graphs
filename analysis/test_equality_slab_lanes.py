from __future__ import annotations

import json
import os
import unittest
from pathlib import Path

from equality_corridor import build_equality_corridor
from equality_slab_lanes import (
    build_census,
    delete_band_and_slab,
    enumerate_minimum_mask_paths,
    extract_cross_slab_signature,
    known_large_trace_deletions,
    mapped_target_depths,
    removed_prefix_u,
)
from tile_grammar import compress_mask
from tile_grammar import advance_row, initial_state


class EqualitySlabLaneTests(unittest.TestCase):
    def test_minimum_path_enumeration_matches_corridor_count(self) -> None:
        corridor = build_equality_corridor(3)
        paths = enumerate_minimum_mask_paths(corridor)
        self.assertEqual(len(paths), 24)
        self.assertEqual(len(set(paths)), 24)

    def test_cross_deletion_geometry_and_depth_mapping(self) -> None:
        masks = (0b11111, 0b10101, 0b01110, 0b00111, 0b11011)
        self.assertEqual(
            delete_band_and_slab(masks, 1, 1),
            (compress_mask(masks[0], 1, 3), compress_mask(masks[4], 1, 3)),
        )
        self.assertEqual(mapped_target_depths(1, 2), (1,))
        self.assertEqual(mapped_target_depths(2, 2), (2, 5))
        self.assertEqual(mapped_target_depths(3, 2), (6,))

    def test_removed_prefix_u_counts_band_slab_union_once(self) -> None:
        masks = (0b11111111,) * 8
        self.assertEqual(removed_prefix_u(masks, 2, 3, 2), 6)
        self.assertEqual(removed_prefix_u(masks, 6, 3, 2), 33)
        self.assertEqual(removed_prefix_u(masks, 8, 3, 2), 39)

    def test_right_boundary_uses_distinct_vertex_and_face_starts(self) -> None:
        target = advance_row(initial_state(8), 0xFF)
        source = advance_row(initial_state(5), 0x1F)
        self.assertIsNotNone(target)
        self.assertIsNotNone(source)
        signature = extract_cross_slab_signature(target, 5, 3)
        self.assertEqual(signature.compressed_previous_u_mask, source.previous_u_mask)
        self.assertEqual(signature.projected_partition, source.partition)
        self.assertEqual(signature.normalized_u_cost, source.u_cost)

    def test_width_six_projection_matches_two_column_frontier(self) -> None:
        target = advance_row(initial_state(8), 0xFF)
        source = advance_row(initial_state(2), 0x03)
        self.assertIsNotNone(target)
        self.assertIsNotNone(source)
        signature = extract_cross_slab_signature(
            target, 2, removed_u_cost=6, slab_width=6
        )
        self.assertEqual(signature.compressed_previous_u_mask, source.previous_u_mask)
        self.assertEqual(signature.projected_partition, source.partition)
        self.assertEqual(signature.normalized_u_cost, source.u_cost)

    def test_cached_census_records_acyclic_decorated_transport(self) -> None:
        artifact = json.loads(Path(__file__).with_name("equality_slab_lanes.json").read_text())
        census = artifact["census"]
        self.assertEqual(census["deletions_tested"], 25_344)
        self.assertEqual(census["direct_optimum_deletions"], 5_704)
        self.assertEqual(census["visible_interface_lanes"], 502)
        self.assertEqual(census["interior_visible_lanes"], 34)
        self.assertEqual(census["closed_projection_lanes"], 0)
        self.assertEqual(census["cycle_preserving_interior_lanes"], 0)
        self.assertEqual(
            census["decoration_transport_graph"],
            {
                "vertices": 27,
                "edges": 19,
                "cycle_offset_stable_lanes": 6,
                "self_loop_lanes": 0,
                "vertices_on_directed_cycles": 0,
            },
        )
        self.assertEqual(artifact["known_large_trace_control"]["exact_deletion_matches"], [])

    def test_known_n14_to_n17_has_no_literal_cross_deletion(self) -> None:
        result = known_large_trace_deletions()
        self.assertEqual(result["deletions_tested"], 225)
        self.assertEqual(result["exact_deletion_matches"], [])

    @unittest.skipUnless(os.environ.get("GRID_GRAPHS_SLOW"), "slow n=5 to n=8 census")
    def test_cached_census_regenerates_exactly(self) -> None:
        artifact = json.loads(Path(__file__).with_name("equality_slab_lanes.json").read_text())
        self.assertEqual(build_census(), artifact)


if __name__ == "__main__":
    unittest.main()
