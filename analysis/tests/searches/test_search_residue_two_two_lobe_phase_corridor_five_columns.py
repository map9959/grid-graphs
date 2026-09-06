from __future__ import annotations

import json
import subprocess
import tempfile
import unittest
from math import comb
from pathlib import Path

from analysis._paths import REPO_ROOT, analysis_path, module_command
from analysis.searches.search_residue_two_middle import KNOWN_249_NEAR
from analysis.searches.search_residue_two_two_lobe_phase_corridor import (
    CAP_DISTRIBUTIONS,
    masks_with_u_count,
)
from analysis.searches.search_residue_two_two_lobe_phase_corridor_five_columns import (
    DEFAULT_RESULT,
    FIXED_BODY_ROWS,
    FROZEN_PACKET_COLUMNS,
    MUTABLE_PACKET_COLUMNS,
    MUTABLE_ROWS,
    mutable_row_words,
    phase_rows,
    provenance,
    row_domains,
    scope,
    validate_scope,
)
from analysis.tests._support import migrated_artifact, slow_test


class FiveColumnTwoLobePhaseCorridorTests(unittest.TestCase):
    def test_exact_widened_scope_and_complete_row_domains(self) -> None:
        rows = phase_rows()
        validate_scope(rows)
        domains = row_domains(rows)
        self.assertEqual(MUTABLE_ROWS, (4, 5, 6, 7, 8, 9, 14, 15, 16, 17))
        self.assertEqual(FIXED_BODY_ROWS, (0, 1, 2, 3, 10, 11, 12, 13))
        self.assertEqual(MUTABLE_PACKET_COLUMNS, (0, 1, 2, 3, 4))
        self.assertEqual(FROZEN_PACKET_COLUMNS, (5,))
        self.assertEqual([len(domains[row]) for row in MUTABLE_ROWS], [114] * 10)
        for row in MUTABLE_ROWS:
            self.assertIn(rows[row], domains[row])
            self.assertIn(KNOWN_249_NEAR[row], domains[row])
            frozen = mutable_row_words(rows, row)[0][5:]
            self.assertTrue(all(word[5:] == frozen for word in mutable_row_words(rows, row)))

    def test_exact_cap_mask_counts(self) -> None:
        self.assertEqual(CAP_DISTRIBUTIONS, ((19, 1), (18, 2), (17, 3)))
        for first, second in CAP_DISTRIBUTIONS:
            self.assertEqual(len(masks_with_u_count(first)), comb(20, first))
            self.assertEqual(len(masks_with_u_count(second)), comb(20, second))

    def test_committed_result_is_a_provenanced_safe_certificate(self) -> None:
        record = migrated_artifact(json.loads(DEFAULT_RESULT.read_text()))
        rows = phase_rows()
        self.assertEqual(record["provenance"], provenance(rows))
        self.assertEqual(record["scope"], scope(rows))
        self.assertIn(record["result"], {"incomplete", "positive", "negative"})
        self.assertEqual(record["result"] == "incomplete", not record["exact"])
        self.assertLessEqual(record["run"]["max_seconds"], 480)
        self.assertIsInstance(record["run"]["elapsed_seconds"], float)
        for expected_row, checkpoint in enumerate(record["completed_body_rows"]):
            self.assertEqual(checkpoint["row"], expected_row)
            self.assertEqual(len(checkpoint["frontier_sha256"]), 64)
            self.assertGreaterEqual(checkpoint["assignments_represented"], checkpoint["outgoing_states"])
        if not record["exact"]:
            self.assertEqual(record["result"], "incomplete")
            self.assertIn("no negative claim", record["run"]["stop_reason"])
            self.assertIsNone(record["witness"])
            self.assertIsNone(record["independent_validation"])

    @slow_test
    def test_one_second_timeout_writes_an_incomplete_certificate(self) -> None:
        script = analysis_path("search_residue_two_two_lobe_phase_corridor_five_columns.py")
        with tempfile.TemporaryDirectory() as directory:
            result = Path(directory) / "result.json"
            witness = Path(directory) / "witness.txt"
            completed = subprocess.run(
                module_command(script) + [
                    "--quiet",
                    "--max-seconds",
                    "1",
                    "--result",
                    str(result),
                    "--witness",
                    str(witness),
                ],
                check=False,
                cwd=REPO_ROOT,
                capture_output=True,
                text=True,
                timeout=10,
            )
            record = migrated_artifact(json.loads(result.read_text()))
            self.assertEqual(completed.returncode, 2)
            self.assertFalse(record["exact"])
            self.assertEqual(record["result"], "incomplete")
            self.assertIn("no negative claim", record["run"]["stop_reason"])
            self.assertFalse(witness.exists())


if __name__ == "__main__":
    unittest.main()
