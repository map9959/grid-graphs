from __future__ import annotations

import json
import unittest

from analysis.searches.search_residue_two_target_recurrence import SCHEDULES, TARGET_U
from analysis.searches.search_residue_two_target_recurrence_attachment import (
    ATTACHMENT_ROWS,
    DEFAULT_OUTPUT,
    PHASES,
    schedule_domains,
)
from analysis.tests._support import migrated_artifact


class TargetRecurrenceAttachmentTests(unittest.TestCase):
    def test_language_strictly_enlarges_only_attachment_rows(self) -> None:
        from analysis.searches.search_residue_two_target_recurrence import schedule_domains as basic_domains

        for phase in ("main_diagonal", "anti_diagonal"):
            for schedule in SCHEDULES:
                basic = basic_domains(schedule, phase)
                enlarged = schedule_domains(schedule, phase)
                self.assertEqual(sum(domain[0].bit_count() for domain in enlarged), TARGET_U)
                for row, (old, new) in enumerate(zip(basic, enlarged, strict=True)):
                    self.assertLessEqual(set(old), set(new))
                    if row in ATTACHMENT_ROWS:
                        self.assertLess(len(old), len(new))
                    else:
                        self.assertEqual(old, new)

    def test_all_declared_domains_have_fixed_charge(self) -> None:
        for phase in PHASES:
            for schedule in SCHEDULES:
                domains = schedule_domains(schedule, phase)
                self.assertEqual(len(domains), 23)
                self.assertEqual(sum(domain[0].bit_count() for domain in domains), TARGET_U)
                self.assertTrue(all(len({mask.bit_count() for mask in domain}) == 1 for domain in domains))

    def test_committed_result_replays_exactly(self) -> None:
        record = migrated_artifact(json.loads(DEFAULT_OUTPUT.read_text()))
        self.assertTrue(record["exact_in_declared_families"])
        self.assertEqual(record["status"], "UNSAT_IN_DECLARED_FAMILIES")
        self.assertIsNone(record["witness"])
        self.assertEqual(len(record["families"]), 2 * len(PHASES))
        for family in record["families"]:
            self.assertEqual(sum(family["row_u_costs"]), TARGET_U)
            result = family["result"]
            self.assertIsNone(result["witness"])
            self.assertEqual(result["conclusion"], "UNSAT_IN_LANGUAGE")
            self.assertEqual(result["connected_state_pairs"], 0)
            self.assertEqual(result["best_profile"], [2, 1])
            expected_pairs = 10_692 if family["schedule"] == "A5_H3_A15" else 7_392
            self.assertEqual(result["tested_state_pairs"], expected_pairs)


if __name__ == "__main__":
    unittest.main()
