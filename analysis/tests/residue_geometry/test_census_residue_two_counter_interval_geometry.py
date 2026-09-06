from __future__ import annotations

import unittest

from analysis.residue_geometry.census_residue_two_counter_interval_geometry import (
    SCHEMA,
    _local_cell_condition,
    build_report,
    census_k,
    replay_choice,
)


class ResidueTwoCounterIntervalGeometryCensusTests(unittest.TestCase):
    def test_local_cell_condition_rejects_diagonal_and_triple(self) -> None:
        self.assertFalse(_local_cell_condition({(0, 0), (1, 1)}, {(0, 0)}, 3))
        self.assertFalse(_local_cell_condition({(0, 0), (0, 1), (1, 0)}, {(0, 0)}, 3))
        self.assertTrue(_local_cell_condition({(0, 0), (0, 1)}, {(0, 0)}, 3))

    def test_each_width_is_fully_classified(self) -> None:
        for k in (7, 8, 9):
            with self.subTest(k=k):
                record = census_k(k)
                histogram = record["rejection_histogram"]
                classified = sum(
                    count for reason, count in histogram.items()
                    if reason not in {
                        "placements",
                        "placement_uses_old_center",
                        "deletion_keeps_old_attachment",
                    }
                )
                self.assertEqual(
                    classified,
                    record["search_space"]["fully_enumerated_edit_choices"],
                )
                self.assertEqual(record["status"], "complete_negative_in_declared_grammar")
                self.assertFalse(record["realizations"])
                sample = record["first_replay_by_terminal_status"]["forbidden_unit_cell"]
                reason, detail = replay_choice(k, sample)
                self.assertEqual(reason, "forbidden_unit_cell")
                self.assertEqual(detail, sample["detail"])

    def test_report_separates_abstract_and_geometric_status(self) -> None:
        report = build_report()
        self.assertEqual(report["schema"], SCHEMA)
        self.assertEqual(report["status"], "complete_negative_in_declared_grammar")
        self.assertIn("remain verified", report["abstract_status"])
        self.assertIn("exhausted", report["geometric_status"])


if __name__ == "__main__":
    unittest.main()
