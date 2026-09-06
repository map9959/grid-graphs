from __future__ import annotations

import json
import subprocess
import tempfile
import unittest
from pathlib import Path

from analysis._paths import REPO_ROOT, analysis_path, module_command
from analysis.searches.search_residue_two_five_column_bidirectional import (
    CUTS,
    DEFAULT_RESULT,
    MUTABLE_H_QUOTA,
    _masks,
    _root,
    _validate_witness,
    compatible_pair_census,
    scope,
)
from analysis.searches.search_residue_two_phase_front import _packet_names
from analysis.searches.search_residue_two_phase_packet_corridor_22 import phase_rows
from analysis.searches.search_residue_two_two_lobe_phase_corridor import MUTABLE_ROWS
from analysis.searches.search_residue_two_two_lobe_phase_corridor_five_columns import (
    row_domains,
)
from analysis.tests._support import migrated_artifact
from analysis.tiles.tile_grammar import advance_row, merge_frontier_profile, row_mask


class FiveColumnBidirectionalTests(unittest.TestCase):
    def test_declared_language_and_quota_cost_identity(self) -> None:
        rows = phase_rows()
        domains = row_domains(rows)
        declared = scope(rows)
        self.assertEqual(CUTS, (8, 9, 13))
        self.assertEqual(declared["mutable_h_quota"], 11)
        self.assertEqual(set(declared["domain_sizes"].values()), {114})
        for row in MUTABLE_ROWS:
            for candidate in domains[row]:
                word = _packet_names(candidate)
                self.assertTrue(word.endswith("R"))
                self.assertEqual(candidate.count("U"), 12 + word.count("H"))

    def test_corrected_phase_front_reflects_and_joins_at_every_cut(self) -> None:
        # This independently exercises reflected masks and the production merge
        # helper at every requested cut, without relying on solver internals.
        candidate = phase_rows()
        for cut in CUTS:
            top = next(iter(_root()[0].values())).state
            for row in candidate[: cut + 1]:
                top = advance_row(top, row_mask(row))
                self.assertIsNotNone(top)
            bottom = next(iter(_root()[0].values())).state
            for row in reversed(candidate[cut + 1 :]):
                bottom = advance_row(bottom, row_mask(row))
                self.assertIsNotNone(bottom)
            self.assertEqual(merge_frontier_profile(top, bottom), (1, 1))

    def test_independent_scope_validation_rejects_invalid_near_geometry(self) -> None:
        from analysis.searches.search_residue_two_middle import KNOWN_249_NEAR

        with self.assertRaisesRegex(AssertionError, "run_check rejected"):
            _validate_witness(KNOWN_249_NEAR, phase_rows(), (18, 2))

    def test_empty_complementary_census_and_root_path(self) -> None:
        root = _root()
        census = compatible_pair_census(root, root)
        self.assertEqual(census["candidate_state_pairs"], 0)
        self.assertEqual(_masks(next(iter(root[0].values()))), [])

    def test_committed_exact_census_and_lane_certificate(self) -> None:
        record = migrated_artifact(json.loads(DEFAULT_RESULT.read_text()))
        self.assertTrue(record["exact"])
        self.assertEqual(record["result"], "negative")
        self.assertEqual(record["chosen_cut"], "9/10")
        self.assertEqual(
            [item["candidate_state_pairs"] for item in record["cut_census"]],
            [10272, 6090, 8928],
        )
        self.assertEqual(
            [lane["name"] for lane in record["lanes"]],
            ["fixed", "all-19-1", "all-18-2", "all-17-3"],
        )
        self.assertTrue(all(lane["census_status"] == "complete" for lane in record["lanes"]))
        self.assertTrue(all(lane["join"]["exact"] for lane in record["lanes"]))
        self.assertEqual(sum(lane["join"]["pairs_checked"] for lane in record["lanes"]), 6090)
        generator = analysis_path("search_residue_two_five_column_bidirectional.py")
        import hashlib

        self.assertEqual(
            record["provenance"]["source_files"]["generator"]["sha256"],
            hashlib.sha256(generator.read_bytes()).hexdigest(),
        )

    def test_memory_guard_is_incomplete_without_negative_claim(self) -> None:
        script = analysis_path("search_residue_two_five_column_bidirectional.py")
        with tempfile.TemporaryDirectory() as directory:
            result_path = Path(directory) / "result.json"
            completed = subprocess.run(
                module_command(script) + [
                    "--quiet",
                    "--max-states",
                    "1",
                    "--max-seconds",
                    "10",
                    "--result",
                    str(result_path),
                ],
                check=False,
                cwd=REPO_ROOT,
                capture_output=True,
                text=True,
                timeout=20,
            )
            guarded = migrated_artifact(json.loads(result_path.read_text()))
        self.assertEqual(completed.returncode, 2)
        self.assertFalse(guarded["exact"])
        self.assertEqual(guarded["result"], "incomplete")
        self.assertIn("exceeded 1 states", guarded["run"]["stop_reason"])
        self.assertIn("no negative claim", guarded["run"]["stop_reason"])


if __name__ == "__main__":
    unittest.main()
