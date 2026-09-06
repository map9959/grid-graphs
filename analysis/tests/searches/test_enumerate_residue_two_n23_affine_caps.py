from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from analysis.searches.enumerate_residue_two_n23_affine_caps import (
    DEFAULT_RESULT,
    SCHEMA,
    census,
    construct_state,
    d4_transforms,
    next_row_stats,
    write_cap_seed,
)
from analysis.patterns.diagonal_patterns import residue_two_affine_pattern
from analysis.tests._support import slow_test
from analysis.tests._support import migrated_artifact


class AffineCapCensusTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.record = migrated_artifact(json.loads(DEFAULT_RESULT.read_text()))

    def test_requested_transition_regressions(self) -> None:
        affine = residue_two_affine_pattern(23)
        depth3 = construct_state(affine[:3])
        self.assertEqual(next_row_stats(depth3, "basic")["live_next_rows"], 0)
        self.assertEqual(next_row_stats(depth3, "phase")["live_next_rows"], 0)

        depth4 = construct_state(affine[:4])
        self.assertEqual(depth4.u_cost, 57)
        self.assertEqual(next_row_stats(depth4, "phase")["live_next_rows"], 212)

        reflected_bottom = construct_state(list(reversed(affine[-2:])))
        self.assertEqual(next_row_stats(reflected_bottom, "phase")["live_next_rows"], 63)
        physical_order = construct_state(affine[-2:])
        self.assertEqual(next_row_stats(physical_order, "phase")["live_next_rows"], 0)

    def test_scope_dedup_and_pairing_are_exactly_declared(self) -> None:
        record = self.record
        self.assertEqual(record["schema"], SCHEMA)
        self.assertEqual(len(d4_transforms(residue_two_affine_pattern(23))), 8)
        self.assertIsNone(record["scope"]["partition_projection"])
        self.assertIsNone(record["scope"]["middle_search"])
        for pairing in record["pairings"]:
            self.assertGreater(pairing["unsearched_gap_rows"], 0)
            self.assertIsNone(pairing["merge_profile"])
            for mode in ("basic", "phase"):
                mode_pairing = pairing["modes"][mode]
                if mode_pairing["representative_pair"] is None:
                    continue
                top_id, bottom_id = mode_pairing["representative_pair"]
                top_depth = str(pairing["top_depth"])
                bottom_depth = str(pairing["bottom_depth"])
                top = next(
                    item for item in record["caps"]["top"][top_depth]["states"]
                    if item["id"] == top_id
                )
                bottom = next(
                    item for item in record["caps"]["bottom"][bottom_depth]["states"]
                    if item["id"] == bottom_id
                )
                self.assertEqual(
                    top["normalized_charge"]
                    + bottom["normalized_charge"]
                    + mode_pairing["representative_required_gap_charge"],
                    pairing["target_total_normalized_charge"],
                )
                self.assertGreater(
                    mode_pairing["one_step_live_full_state_pairs"], 0
                )

    def test_all_ordered_depth_pairs_are_present(self) -> None:
        pairs = {
            (item["top_depth"], item["bottom_depth"])
            for item in self.record["pairings"]
            if item["target_u"] == 332
        }
        self.assertEqual(pairs, {(top, bottom) for top in range(2, 7) for bottom in range(2, 7)})

    @slow_test
    def test_committed_census_reproduces(self) -> None:
        self.assertEqual(self.record, census())

    def test_optional_output_is_labeled_cap_seed_not_witness(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "seed.json"
            write_cap_seed(self.record, path, 332)
            seed = migrated_artifact(json.loads(path.read_text()))
            self.assertEqual(seed["label"], "cap seed, not witness")
            self.assertGreater(seed["unsearched_gap_rows"], 0)


if __name__ == "__main__":
    unittest.main()
