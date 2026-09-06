from __future__ import annotations

import json
import tempfile
import unittest
from dataclasses import replace
from pathlib import Path

from analysis.patterns.construction_lab import (
    dual_connectivity_check,
    forest_completion_check,
)
from analysis.patterns.construction_lab import (
    q_old_formula as q_formula,
)
from analysis.searches.search_residue_two_phase_front import (
    DEFAULT_RESULT,
    DEFAULT_WITNESS,
    RESULT_SCHEMA,
    SearchResult,
    _rows_sha256,
    result_json,
    search,
    write_artifacts,
)
from analysis.tests._support import migrated_artifact, slow_test


class PhaseFrontArtifactTests(unittest.TestCase):
    def test_committed_witness_is_the_reported_unicyclic_witness(self) -> None:
        record = migrated_artifact(json.loads(DEFAULT_RESULT.read_text()))
        rows = DEFAULT_WITNESS.read_text().splitlines()
        search = record["searches"][0]

        self.assertEqual(record["schema"], RESULT_SCHEMA)
        self.assertEqual(search["witness"], rows)
        self.assertEqual(sum(row.count("U") for row in rows), search["target_u"])
        self.assertTrue(dual_connectivity_check(rows)[0])
        self.assertTrue(forest_completion_check(rows)[0])

        n = len(rows)
        dual_edges = sum(
            rows[r][c] == rows[r][c + 1] == "U"
            for r in range(n)
            for c in range(n - 1)
        ) + sum(
            rows[r][c] == rows[r + 1][c] == "U"
            for r in range(n - 1)
            for c in range(n)
        )
        self.assertEqual(dual_edges - (1 + (n - 1) ** 2) + 1, 1)
        self.assertEqual(search["best_join"], [1, 1])
        self.assertEqual(record["output"]["witness"]["sha256"], _rows_sha256(rows))

    @slow_test
    def test_committed_result_and_witness_reproduce(self) -> None:
        record = migrated_artifact(json.loads(DEFAULT_RESULT.read_text()))
        rerun = record["output"]["rerun"]
        fresh = search(
            rerun["n"],
            q_formula(rerun["n"]) + rerun["surplus"],
            mode=rerun["mode"],
            beam=rerun["beam"],
            split=rerun["split"],
            report=False,
        )
        self.assertEqual(result_json([fresh])["searches"][0], record["searches"][0])
        self.assertEqual(fresh.witness, DEFAULT_WITNESS.read_text().splitlines())

    def test_negative_removes_only_a_witness_owned_by_prior_result(self) -> None:
        positive = SearchResult(
            20, q_formula(20) + 1, "basic", "test", "positive", 1, 8, 1,
            1, 1, 1, 1, (1, 1), 1, 1, None, ["U"], (),
        )
        negative = replace(positive, conclusion="negative", witness=None)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            result_path = root / "result.json"
            witness_path = root / "witness.txt"
            write_artifacts(positive, result_path, witness_path)
            self.assertTrue(witness_path.exists())

            record = write_artifacts(negative, result_path, witness_path)
            self.assertFalse(witness_path.exists())
            self.assertEqual(record["output"]["witness"]["status"], "removed_prior_generated")

            witness_path.write_text("unrelated\n")
            record = write_artifacts(negative, result_path, witness_path)
            self.assertEqual(witness_path.read_text(), "unrelated\n")
            self.assertEqual(
                record["output"]["witness"]["status"], "stale_unmanaged_not_current"
            )


if __name__ == "__main__":
    unittest.main()
