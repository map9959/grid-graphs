from __future__ import annotations

import json
import unittest

from analysis.searches.analyze_residue_two_b23_cut_repairs import DEFAULT_OUTPUT, INPUT, rows_sha256
from analysis.patterns.construction_lab import dual_connectivity_check
from analysis.searches.search_residue_two_target_control import changed_rows
from analysis.tests._support import migrated_artifact


class ResidueTwoB23CutRepairTests(unittest.TestCase):
    def test_scope_is_exact_but_not_global(self) -> None:
        result = migrated_artifact(json.loads(DEFAULT_OUTPUT.read_text(encoding="ascii")))
        self.assertEqual(result["status"], "UNSAT_IN_DECLARED_CUT_REPAIR_NEIGHBORHOOD")
        self.assertTrue(result["exact_in_declared_scope"])
        self.assertIn("not a global n=23 impossibility", result["scope"]["negative_claim"])
        self.assertEqual(result["witness_count"], 0)

        replays = [
            replay
            for example in result["examples"]
            for order in example["orders"]
            for replay in order["final_replays"]
        ]
        self.assertGreater(len(replays), 0)
        self.assertTrue(all(not replay["dual_connected"] for replay in replays))

    def test_final_tuple_independently_replays(self) -> None:
        result = migrated_artifact(json.loads(DEFAULT_OUTPUT.read_text(encoding="ascii")))
        source = migrated_artifact(json.loads(INPUT.read_text(encoding="ascii")))
        rows_by_hash = {
            example["sha256"]: example["rows"]
            for example in source["budgets"]["333"]["best_examples"]
        }
        tested = 0
        for example in result["examples"]:
            rows = rows_by_hash[example["source_sha256"]]
            for order in example["orders"]:
                for replay in order["final_replays"]:
                    candidate = changed_rows(
                        rows,
                        tuple(map(tuple, replay["additions"])),
                        tuple(map(tuple, replay["removals"])),
                    )
                    self.assertEqual(sum(row.count("U") for row in candidate), 333)
                    self.assertEqual(rows_sha256(candidate), replay["sha256"])
                    self.assertEqual(dual_connectivity_check(candidate)[0], replay["dual_connected"])
                    tested += 1
        self.assertEqual(tested, 1)


if __name__ == "__main__":
    unittest.main()
