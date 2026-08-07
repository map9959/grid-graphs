from __future__ import annotations

import json
import itertools
import unittest

from construction_lab import dual_connectivity_check, forest_completion_check, run_check
from search_residue_two_target_control import (
    DEFAULT_INPUT,
    DEFAULT_OUTPUT,
    ConnectivitySensitivity,
    changed_rows,
    load_source,
    rows_sha256,
)


class TargetControlTests(unittest.TestCase):
    def test_committed_source_and_scoped_negative_replay(self) -> None:
        rows = load_source(DEFAULT_INPUT)
        result = json.loads(DEFAULT_OUTPUT.read_text())

        self.assertEqual(result["source"]["sha256"], rows_sha256(rows))
        self.assertEqual(result["status"], "UNSAT_IN_DECLARED_NEIGHBORHOOD")
        self.assertTrue(result["exact_in_declared_neighborhood"])
        self.assertEqual(result["scope"]["target_u"], 333)
        self.assertTrue(dual_connectivity_check(rows)[0])
        self.assertTrue(forest_completion_check(rows)[0])
        self.assertTrue(run_check(23, rows, expected_u=335)["all_ok"])

        deletion, one_addition, two_additions, three_additions = result["orders"]
        self.assertEqual(deletion["candidate_removal_tuples_tested"], 55_945)
        self.assertEqual(deletion["dual_connected"], 0)
        self.assertEqual(one_addition["addition_sets"], 194)
        self.assertEqual(one_addition["candidate_removal_tuples_tested"], 1)
        self.assertEqual(one_addition["dual_connected"], 0)
        self.assertEqual(sum(one_addition["individual_candidate_count_histogram"].values()), 194)
        self.assertEqual(two_additions["addition_sets"], 18_721)
        self.assertEqual(two_additions["candidate_removal_tuples_tested"], 202)
        self.assertEqual(two_additions["dual_connected"], 0)
        self.assertEqual(two_additions["forest_completable"], 0)
        self.assertEqual(
            two_additions["individual_candidate_count_histogram"],
            {"0": 13_197, "1": 3_168, "2": 1_820, "3": 442, "4": 67, "5": 27},
        )
        self.assertEqual(
            sum(two_additions["individual_candidate_count_histogram"].values()), 18_721
        )
        self.assertEqual(three_additions["addition_sets"], 1_198_144)
        self.assertEqual(three_additions["addition_sets_assigned_to_shard"], 1_198_144)
        self.assertEqual(three_additions["pair_optimistic_prefilter_pruned"], 7_379)
        self.assertEqual(three_additions["qualifying_addition_sets"], 6_902)
        self.assertEqual(three_additions["candidate_removal_tuples_tested"], 15_057)
        self.assertEqual(three_additions["dual_connected"], 0)
        self.assertEqual(three_additions["forest_completable"], 0)
        self.assertEqual(three_additions["dual_connected_survivors"], [])
        self.assertEqual(
            three_additions["individual_candidate_count_histogram"],
            {
                "0": 689_438,
                "1": 258_462,
                "2": 160_607,
                "3": 60_193,
                "4": 15_163,
                "5": 5_971,
                "6": 756,
                "7": 158,
                "8": 13,
                "9": 4,
            },
        )
        self.assertEqual(
            sum(three_additions["individual_candidate_count_histogram"].values())
            + three_additions["pair_optimistic_prefilter_pruned"],
            1_198_144,
        )
        self.assertEqual(
            three_additions["qualifying_controls_sha256"],
            "d0565e8c04a6a7bb70fdbd9a4181894322981632685823fffb30615574433983",
        )
        self.assertEqual(result["witnesses"], [])

    def test_sole_order_one_triple_independently_disconnects(self) -> None:
        rows = load_source(DEFAULT_INPUT)
        result = json.loads(DEFAULT_OUTPUT.read_text())
        controls = result["orders"][1]["qualifying_individual_controls"]
        triples = [control for control in controls if len(control["individually_removable"]) == 3]

        self.assertEqual(len(triples), 1)
        control = triples[0]
        additions = tuple(map(tuple, control["additions"]))
        removals = tuple(map(tuple, control["individually_removable"]))
        augmented = changed_rows(rows, additions, ())
        self.assertTrue(all(
            dual_connectivity_check(changed_rows(augmented, (), (cell,)))[0]
            for cell in removals
        ))
        candidate = changed_rows(augmented, (), removals)
        self.assertEqual(sum(row.count("U") for row in candidate), 333)
        self.assertFalse(dual_connectivity_check(candidate)[0])

    def test_every_order_two_final_candidate_independently_disconnects(self) -> None:
        rows = load_source(DEFAULT_INPUT)
        result = json.loads(DEFAULT_OUTPUT.read_text())
        controls = result["orders"][2]["qualifying_individual_controls"]
        tested = 0
        for control in controls:
            additions = tuple(map(tuple, control["additions"]))
            augmented = changed_rows(rows, additions, ())
            removable = tuple(map(tuple, control["individually_removable"]))
            for removals in itertools.combinations(removable, 4):
                tested += 1
                candidate = changed_rows(augmented, (), removals)
                self.assertEqual(sum(row.count("U") for row in candidate), 333)
                self.assertFalse(dual_connectivity_check(candidate)[0])
        self.assertEqual(tested, 202)

    def test_sensitivity_queries_agree_with_canonical_connectivity(self) -> None:
        rows = load_source(DEFAULT_INPUT)
        sensitivity = ConnectivitySensitivity(rows)
        additions_to_check = (
            ((0, 0),),
            ((9, 15),),
            ((0, 0), (9, 15)),
            ((2, 5), (15, 17)),
            ((0, 0), (0, 2), (10, 17)),
        )
        for additions in additions_to_check:
            augmented = changed_rows(rows, additions, ())
            fast = set(sensitivity.individually_removable(additions))
            canonical = {
                cell
                for cell in sensitivity.source_u
                if dual_connectivity_check(changed_rows(augmented, (), (cell,)))[0]
            }
            self.assertEqual(fast, canonical)


if __name__ == "__main__":
    unittest.main()
