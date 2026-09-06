from __future__ import annotations

import json
import unittest

from analysis.bounds.wave2_occurrence_hall_micro_census import (
    ORIENTATIONS,
    CensusBounds,
    Demand,
    Template,
    enumerate_templates,
    exact_hall_check,
    neighborhoods,
    replay_certificate,
    run_policy_census,
    template_from_json,
    template_json,
    trace,
)
from analysis.tests._support import migrated_artifact


class Wave2OccurrenceHallMicroCensusTests(unittest.TestCase):
    def setUp(self) -> None:
        # Distinct starts and histories reconverge at the north gap (-1, 1).
        self.reconvergent = Template(
            orientation="north",
            depth=1,
            multiplicity=1,
            starts=(0, 2),
            histories=((1,), (-1,)),
        )

    def test_reconvergence_preserves_occurrence_labels(self) -> None:
        demands = self.reconvergent.demands()
        self.assertEqual(
            demands,
            (Demand(0, 0, (1,)), Demand(1, 2, (-1,))),
        )
        self.assertEqual(trace(self.reconvergent, demands[0])[-1], trace(self.reconvergent, demands[1])[-1])

        immediate = exact_hall_check(self.reconvergent, "immediate-local")
        self.assertFalse(immediate["hall"])
        self.assertEqual(immediate["violating_indices"], [0, 1])
        self.assertTrue(replay_certificate(self.reconvergent, "immediate-local", immediate))

    def test_transported_basin_routes_reconvergent_occurrences(self) -> None:
        candidates = neighborhoods(self.reconvergent, "transported-basin")
        self.assertEqual(candidates[0], candidates[1])
        self.assertEqual(len(candidates[0]), 3)
        certificate = exact_hall_check(self.reconvergent, "transported-basin")
        self.assertTrue(certificate["hall"])
        self.assertTrue(replay_certificate(self.reconvergent, "transported-basin", certificate))

        round_trip = migrated_artifact(json.loads(json.dumps(template_json(self.reconvergent))))
        rebuilt = template_from_json(round_trip)
        replayed = migrated_artifact(json.loads(json.dumps(certificate)))
        self.assertEqual(rebuilt, self.reconvergent)
        self.assertTrue(replay_certificate(rebuilt, "transported-basin", replayed))

    def test_transported_basin_still_fails_with_unpaid_multiplicity(self) -> None:
        repeated = Template(
            orientation="north",
            depth=1,
            multiplicity=2,
            starts=(0, 1, 2),
            histories=((1,), (-1,), (-1,)),
        )
        certificate = exact_hall_check(repeated, "transported-basin")
        self.assertFalse(certificate["hall"])
        self.assertEqual(certificate["demand_count"], 4)
        self.assertEqual(certificate["neighborhood_count"], 3)
        self.assertTrue(
            replay_certificate(repeated, "transported-basin", certificate)
        )

    def test_all_orientations_and_occurrence_multiplicity_are_enumerated(self) -> None:
        templates = list(
            enumerate_templates(CensusBounds(1, 2, 2, 6, 100))
        )
        self.assertEqual({template.orientation for template in templates}, set(ORIENTATIONS))
        repeated = next(template for template in templates if template.multiplicity == 2)
        first, second = repeated.demands()
        self.assertNotEqual(first.origin_id, second.origin_id)
        self.assertEqual((first.start, first.transition_history), (second.start, second.transition_history))

    def test_statuses_distinguish_counterexample_complete_and_cap(self) -> None:
        counterexample = run_policy_census(
            CensusBounds(1, 1, 3, 6, 100), "immediate-local"
        )
        self.assertEqual(counterexample["status"], "counterexample_found")

        complete = run_policy_census(
            CensusBounds(1, 1, 1, 2, 100), "transported-basin"
        )
        self.assertEqual(complete["status"], "all_templates_satisfy_within_declared_family")
        self.assertIsNotNone(complete["last_matching"])

        capped = run_policy_census(
            CensusBounds(1, 1, 1, 2, 1), "transported-basin"
        )
        self.assertEqual(capped["status"], "incomplete_due_to_cap")

        with self.assertRaisesRegex(ValueError, "template_cap must be in"):
            CensusBounds(template_cap=50_001).validate()


if __name__ == "__main__":
    unittest.main()
