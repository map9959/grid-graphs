from __future__ import annotations

import json
import unittest

from analysis.patterns.construction_lab import (
    dual_connectivity_check,
    forest_completion_check,
)
from analysis.searches.n23_target_search import (
    AFFINE_WINDOW,
    DEFAULT_OUTPUT,
    SCHEMA,
    SYMBOLIC_WINDOW,
    rows_sha256,
)
from analysis.tests._support import migrated_artifact


class N23TargetSearchTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.result = migrated_artifact(json.loads(DEFAULT_OUTPUT.read_text()))

    def test_committed_sources_replay(self) -> None:
        result = self.result
        self.assertEqual(result["schema"], SCHEMA)
        self.assertTrue(result["exact_in_declared_scope"])
        self.assertEqual(result["status"], "UNSAT_IN_DECLARED_FINITE_NEIGHBORHOODS")
        for key in ("affine_source", "symbolic_source"):
            source = result[key]
            self.assertEqual(rows_sha256(source["rows"]), source["sha256"])
            self.assertEqual(sum(row.count("U") for row in source["rows"]), source["u_count"])
            self.assertEqual(dual_connectivity_check(source["rows"])[0], source["dual_connected"])
            self.assertEqual(forest_completion_check(source["rows"])[0], source["forest_completable"])

    def test_exact_counts_and_scopes(self) -> None:
        result = self.result
        deletion, remove3_add1, remove4_add2 = result["affine_searches"]
        self.assertEqual(deletion["generated"], 55_945)
        self.assertEqual(deletion["canonical_dual_checks"], 55_945)
        self.assertEqual((deletion["dual_connected"], deletion["forest_completable"]), (0, 0))
        self.assertEqual(len(AFFINE_WINDOW), 49)
        self.assertEqual((remove3_add1["eligible_additions"], remove3_add1["eligible_removals"]), (14, 35))
        self.assertEqual((remove3_add1["addition_sets"], remove3_add1["candidate_removal_tuples_tested"]), (14, 0))
        self.assertEqual((remove4_add2["addition_sets"], remove4_add2["candidate_removal_tuples_tested"]), (91, 0))

        self.assertEqual(len(SYMBOLIC_WINDOW), 241)
        one, two = result["symbolic_searches"]
        self.assertEqual((one["eligible_additions"], one["eligible_removals"]), (89, 152))
        self.assertEqual((one["addition_sets"], one["connected_after_additions"]), (89, 0))
        self.assertEqual((two["addition_sets"], two["connected_after_additions"]), (3_916, 0))
        self.assertEqual(one["candidate_removal_tuples_tested"], 0)
        self.assertEqual(two["candidate_removal_tuples_tested"], 0)
        self.assertEqual(result["witnesses"], [])
        self.assertEqual(result["n26_open_slab_investigation"], "not_run_no_n23_witness")


if __name__ == "__main__":
    unittest.main()
