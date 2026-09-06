from __future__ import annotations

import json
import unittest

from analysis.searches.analyze_residue_two_b_state import DEFAULT_OUTPUT, analyze
from analysis.patterns.construction_lab import dual_connectivity_check, forest_completion_check
from analysis.patterns.diagonal_patterns import residue_two_affine_pattern
from analysis.searches.search_residue_two_b_state_phase_pump import (
    DEFAULT_OUTPUT as PUMP_DEFAULT,
    dual_diagnostics,
    row_domains,
)
from analysis.tiles.tile_grammar import row_mask
from analysis.tests._support import migrated_artifact


class BStateArtifactTests(unittest.TestCase):
    def test_dual_diagnostics_agree_with_affine_control(self) -> None:
        diagnostic = dual_diagnostics(residue_two_affine_pattern(23))

        self.assertEqual(diagnostic["u_count"], 335)
        self.assertEqual(diagnostic["component_count"], 1)
        self.assertEqual(diagnostic["cycle_excess"], 5)
        self.assertEqual(len(diagnostic["deterministic_redundant_edges"]), 5)
        self.assertEqual(diagnostic["missing_cut_edges"], [])
        self.assertTrue(diagnostic["forest_ok"])

    def test_targeted_s_domains_are_calibrated_basic_supersets(self) -> None:
        _, affine, _, basic = row_domains(3, "basic")
        _, _, _, targeted = row_domains(3, "targeted")

        self.assertTrue(all(set(left) <= set(right) for left, right in zip(basic, targeted, strict=True)))
        self.assertTrue(all(len(right) == 1 for right in targeted[:6] + targeted[17:]))
        self.assertTrue(all(
            row_mask(row) in domain for row, domain in zip(affine, targeted, strict=True)
        ))

    def test_declared_control_is_reproduced(self) -> None:
        committed = migrated_artifact(json.loads(DEFAULT_OUTPUT.read_text()))
        fresh = analyze()

        self.assertEqual(fresh, committed)
        self.assertEqual((fresh["a17"]["u_count"], fresh["b20"]["u_count"]), (179, 250))
        self.assertEqual((fresh["a17"]["surplus"], fresh["b20"]["surplus"]), (1, 1))
        self.assertEqual((fresh["a17"]["cycle_excess"], fresh["b20"]["cycle_excess"]), (1, 1))
        self.assertEqual(fresh["a17_to_b20_alignment"]["minimum_strict_radius"], 3)
        self.assertEqual(fresh["b20_to_affine23_alignment"]["minimum_strict_radius"], 3)

    def test_terminal_artifacts_exhibit_one_missing_attachment(self) -> None:
        dump = migrated_artifact(json.loads((DEFAULT_OUTPUT.parent / "frontier_n17_u178_step287.json").read_text()))
        replay = migrated_artifact(json.loads((DEFAULT_OUTPUT.parent / "frontier_n17_u179_replay.json").read_text()))
        states = dump["states"]

        self.assertEqual(len(states), 20)
        self.assertEqual({(state["cost"], tuple(state["labels"])) for state in states}, {(177, (0, 1, 2))})
        outcomes = [state["next_transitions"][1]["outcome"] for state in states]
        self.assertEqual(outcomes.count("retired_component"), 2)
        self.assertEqual(outcomes.count("rank"), 18)
        step287 = next(record for record in replay["records"] if record["completed_steps"] == 287)
        step288 = next(record for record in replay["records"] if record["completed_steps"] == 288)
        self.assertEqual((step287["cost"], step287["labels"]), (178, [0, 0, 1]))
        self.assertEqual((step288["cost"], step288["labels"]), (179, [0, 0]))
        self.assertTrue(replay["accepted"])

    def test_basic_pump_result_has_positive_control_and_scoped_negative(self) -> None:
        path = PUMP_DEFAULT.with_name("residue_two_b20_to_b23_basic_result.json")
        record = migrated_artifact(json.loads(path.read_text()))
        positive = record["budgets"]["335"]
        negative = record["budgets"]["333"]

        self.assertEqual(record["mode"], "basic")
        self.assertTrue(record["affine_335_in_every_row_domain"])
        self.assertEqual(positive["conclusion"], "SAT")
        self.assertEqual(positive["validation"]["u_count"], 335)
        self.assertTrue(dual_connectivity_check(positive["witness"])[0])
        self.assertTrue(forest_completion_check(positive["witness"])[0])
        self.assertEqual(negative["conclusion"], "UNSAT_IN_LANGUAGE")
        self.assertEqual(negative["connected_state_pairs"], 0)
        self.assertIsNone(negative["witness"])

    def test_targeted_and_full_phase_results_remain_calibrated_negative(self) -> None:
        targeted = migrated_artifact(json.loads(
            (DEFAULT_OUTPUT.parent / "residue_two_b20_to_b23_targeted_result.json").read_text()
        ))
        compiled = migrated_artifact(json.loads(
            (DEFAULT_OUTPUT.parent / "residue_two_b20_to_b23_phase_compiled_result.json").read_text()
        ))

        self.assertEqual(targeted["budgets"]["335"]["connected_state_pairs"], 705)
        self.assertEqual(targeted["budgets"]["333"]["connected_state_pairs"], 0)
        self.assertTrue(compiled["exact_in_declared_language"])
        self.assertEqual(compiled["budgets"]["335"]["connected_state_pairs"], 705)
        self.assertEqual(compiled["budgets"]["333"]["tested_state_pairs"], 238)
        self.assertEqual(compiled["budgets"]["333"]["connected_state_pairs"], 0)
        self.assertEqual(compiled["budgets"]["333"]["best_components"], 3)
        self.assertEqual(
            compiled["calibration"]["python_top_states"],
            compiled["calibration"]["rust_top_states"],
        )
        self.assertEqual(
            compiled["calibration"]["python_bottom_states"],
            compiled["calibration"]["rust_bottom_states"],
        )

    def test_near_miss_bridge_exchanges_are_negative(self) -> None:
        exchanges = migrated_artifact(json.loads(
            (DEFAULT_OUTPUT.parent / "residue_two_b23_near_miss_exchanges.json").read_text()
        ))

        self.assertEqual(len(exchanges["examples"]), 3)
        self.assertEqual(exchanges["witness_count"], 0)
        self.assertTrue(all(not example["witnesses"] for example in exchanges["examples"]))


if __name__ == "__main__":
    unittest.main()
