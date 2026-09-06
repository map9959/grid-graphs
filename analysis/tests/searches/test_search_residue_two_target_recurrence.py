from __future__ import annotations

import json
import unittest

from analysis.patterns.construction_lab import run_check
from analysis.searches.search_residue_two_target_recurrence import (
    DEFAULT_OUTPUT,
    DIRECT_SCHEDULES,
    SCHEDULES,
    TARGET_U,
    hold_rows,
    schedule_domains,
)
from analysis.tests._support import migrated_artifact


class TargetRecurrenceTests(unittest.TestCase):
    def test_domains_have_the_exact_recurrence_charge(self) -> None:
        self.assertEqual(len(hold_rows()), 65)
        self.assertEqual({row.count("U") for row in hold_rows()}, {15})
        for phase in ("main_diagonal", "anti_diagonal"):
            for schedule in (*SCHEDULES, *DIRECT_SCHEDULES):
                domains = schedule_domains(schedule, phase)
                self.assertEqual(len(domains), 23)
                self.assertEqual(sum(domain[0].bit_count() for domain in domains), TARGET_U)
                self.assertTrue(all(len({mask.bit_count() for mask in domain}) == 1 for domain in domains))

    def test_committed_result_has_exact_scoped_replays(self) -> None:
        record = migrated_artifact(json.loads(DEFAULT_OUTPUT.read_text()))
        self.assertTrue(record["exact_in_declared_families"])
        self.assertEqual(record["status"], "UNSAT_IN_DECLARED_FAMILIES")
        self.assertEqual(len(record["families"]), 12)
        for family in record["families"]:
            self.assertEqual(sum(family["row_u_costs"]), TARGET_U)
            result = family["result"]
            if result["witness"] is not None:
                self.assertTrue(run_check(23, result["witness"], expected_u=TARGET_U)["all_ok"])
            else:
                self.assertEqual(result["conclusion"], "UNSAT_IN_LANGUAGE")
                self.assertEqual(result["connected_state_pairs"], 0)

        by_key = {
            (family["phase"], family["schedule"]): family
            for family in record["families"]
        }
        for phase in ("main_diagonal", "anti_diagonal"):
            early = by_key[(phase, "A5_H3_A15")]
            near = by_key[(phase, "A8_H3_A12")]
            direct = by_key[(phase, "direct_P5_P5")]
            self.assertEqual(early["result"]["tested_state_pairs"], 10_604)
            self.assertEqual(early["result"]["best_profile"], [2, 1])
            self.assertEqual(near["result"]["tested_state_pairs"], 7_260)
            self.assertEqual(near["result"]["best_profile"], [2, 1])
            self.assertEqual(direct["result"]["tested_state_pairs"], 3_828)
            self.assertEqual(direct["result"]["best_profile"], [3, 1])


if __name__ == "__main__":
    unittest.main()
