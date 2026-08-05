from __future__ import annotations

import json
import os
import unittest
from pathlib import Path

from equality_composed_transport import build_census


class EqualityComposedTransportTests(unittest.TestCase):
    def test_cached_census_records_cap_and_multiband_composition(self) -> None:
        artifact = json.loads(
            Path(__file__).with_name("equality_composed_transport.json").read_text()
        )
        cap = artifact["cap_mediated_composition"]
        self.assertEqual(cap["joined_intermediate_paths"], 10)
        self.assertEqual(cap["source_intermediate_target_triples"], 80)
        self.assertEqual(cap["alignment_chains"], 49_638)
        self.assertEqual(cap["cycle_preserving_joined_intermediate_paths"], 4)
        self.assertEqual(cap["cycle_preserving_triples"], 8)
        self.assertEqual(cap["cycle_preserving_alignment_chains"], 2_832)

        direct = artifact["direct_multiband_comparison"]
        self.assertEqual(direct["composed_source_target_pairs"], 53)
        self.assertEqual(direct["common_source_target_pairs"], 53)
        self.assertEqual(
            direct["cycle_preserving_common_source_target_pairs"], 6
        )

        continuation = artifact["fixed_n11_continuation_control"]
        self.assertEqual(continuation["cap_reachable_source_paths"], 58)
        self.assertEqual(continuation["successful_source_orientation_pairs"], 0)
        self.assertEqual(continuation["alignment_paths"], 0)

    @unittest.skipUnless(
        os.environ.get("GRID_GRAPHS_SLOW"), "slow composed-transport census"
    )
    def test_cached_census_regenerates_exactly(self) -> None:
        artifact = json.loads(
            Path(__file__).with_name("equality_composed_transport.json").read_text()
        )
        self.assertEqual(build_census(), artifact)


if __name__ == "__main__":
    unittest.main()
