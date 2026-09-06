from __future__ import annotations

import json
import os
import unittest
from collections import Counter
from fractions import Fraction

from analysis.residue_certificates.residue_two_silent_hull_potential_experiment import (
    DEFAULT_OUTPUT,
    STAGES,
    WIDTHS,
    _affine_rref,
    _edge_weight,
    _lift_candidate,
    _potential,
    build_artifact,
    structural_terms,
)
from analysis.tests._support import migrated_artifact
from analysis.tiles.tile_grammar import FrontierState, advance_row, initial_state
from analysis.transport.equality_corridor import structural_key


class ResidueTwoSilentHullPotentialExperimentTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.artifact = migrated_artifact(json.loads(DEFAULT_OUTPUT.read_text()))

    def test_scope_and_model_are_explicitly_bounded_and_structural(self) -> None:
        self.assertEqual(WIDTHS, (5, 8))
        self.assertEqual(STAGES, ("atom-sum", "adjacent-bigrams", "finite-parser"))
        scope = self.artifact["scope"]
        self.assertEqual(scope["complete_equality_training_widths"], [5, 8])
        self.assertEqual(scope["complete_reachable_and_completable_evaluation_widths"], [5, 8])
        self.assertFalse(scope["larger_widths_used"])
        self.assertFalse(scope["annulus_data_used"])
        self.assertFalse(scope["arbitrary_width_coverage_claimed"])
        self.assertTrue(scope["tight_equality_corridor_edges_assumed"])
        self.assertEqual(
            scope["infeasibility_conclusion"],
            "reported separately for each declared feature class",
        )
        excluded = self.artifact["model"]["excluded_features"]
        self.assertEqual(excluded, ["cumulative U", "cumulative rank", "cumulative K", "forward distance"])

    def test_terms_are_only_declared_finite_control_and_atom_occurrences(self) -> None:
        terms = structural_terms(initial_state(5))
        self.assertEqual(terms["cap:00"], 1)
        self.assertEqual(terms["phase:top"], 1)
        self.assertEqual(terms["left-role:absent"], 1)
        self.assertTrue(all(name.startswith(("cap:", "phase:", "left-role:", "cap-phase-left-role:", "atom:")) for name in terms))
        self.assertNotIn("u_cost", " ".join(terms))
        bigrams = structural_terms(initial_state(5), "adjacent-bigrams")
        self.assertTrue(any(name.startswith("bigram:") for name in bigrams))
        parser = structural_terms(initial_state(5), "finite-parser")
        self.assertTrue(any(name.startswith("parser-transition:") for name in parser))
        self.assertTrue(any(name.startswith("parser-accept:") for name in parser))

    def test_potential_uses_exact_fraction_arithmetic_and_zero_for_unseen_terms(self) -> None:
        terms = Counter({"cap:00": 1, "atom:unseen": 3})
        self.assertEqual(_potential(terms, {"cap:00": Fraction(1, 3)}), Fraction(1, 3))

    def test_affine_rref_returns_exact_particular_and_nullspace_coordinates(self) -> None:
        rows = [[Fraction(1), Fraction(2), Fraction(-1)]]
        rhs = [Fraction(3)]
        particular, forms, free_columns, _, diagnostics = _affine_rref(rows, rhs)
        self.assertEqual(particular, [Fraction(3), Fraction(0), Fraction(0)])
        self.assertEqual(free_columns, [1, 2])
        self.assertEqual(diagnostics["nullity"], 2)
        candidate = _lift_candidate(forms, [Fraction(2), Fraction(5)])
        self.assertEqual(sum(a * b for a, b in zip(rows[0], candidate)), rhs[0])

    def test_artifact_reports_fit_and_exhaustive_bounded_evaluation(self) -> None:
        stages = self.artifact["exact_equality_fit_stages"]
        self.assertEqual([stage["stage"] for stage in stages], list(STAGES))
        failed, bigram, parser = stages
        self.assertFalse(failed["exact_equalities_satisfied"])
        certificate = failed["exact_linear_inconsistency_certificate"]
        self.assertEqual(certificate["left_side"], [0, 1])
        self.assertEqual(certificate["right_side"], [1, 1])
        self.assertTrue(bigram["exact_equalities_satisfied"])
        self.assertEqual(
            (bigram["terms_observed_in_training"], bigram["rank"], bigram["free_variables"]),
            (617, 310, 307),
        )
        self.assertTrue(parser["exact_equalities_satisfied"])
        self.assertEqual(
            (parser["terms_observed_in_training"], parser["rank"], parser["free_variables"]),
            (920, 312, 608),
        )
        self.assertEqual(self.artifact["model"]["stages_analyzed"], list(STAGES))
        self.assertEqual(
            self.artifact["status"],
            "finite-parser:exactly-infeasible-under-tight-equality-anchors",
        )
        results = self.artifact["stage_results"]
        self.assertEqual(results["atom-sum"]["status"], "equality-system-inconsistent")
        self.assertEqual(
            results["adjacent-bigrams"]["status"],
            "exactly-infeasible-under-tight-equality-anchors",
        )
        self.assertIsNotNone(results["adjacent-bigrams"]["exact_infeasibility_certificate"])
        self.assertEqual(
            results["finite-parser"]["status"],
            "exactly-infeasible-under-tight-equality-anchors",
        )
        self.assertIsNotNone(results["finite-parser"]["exact_infeasibility_certificate"])
        self.assertIn("suggested_additional_structural_context", results["finite-parser"])
        highs = results["finite-parser"]["highs_search"]
        self.assertEqual(highs["binary"], "/tmp/opencode/bin/highs")
        self.assertEqual(highs["version"], "1.15.1")
        self.assertEqual(highs["free_variables"], 608)
        self.assertEqual(highs["exported_rows"], 427411)
        self.assertEqual(highs["exported_nonzeros"], 12521065)
        self.assertFalse(highs["exact_feasible_rational_candidate_found"])
        self.assertEqual(highs["runs"][0]["solver_status"], "infeasible-diagnostic-only")
        self.assertEqual(highs["runs"][0]["returncode"], 0)
        self.assertEqual(
            highs["runs"][0]["command"][0], "/tmp/opencode/bin/highs"
        )
        self.assertIn("diagnostic only", highs["infeasible_status_policy"])
        ray = highs["exact_ray_extraction"]
        self.assertEqual(ray["status"], "exact-certificate")
        self.assertEqual(ray["floating_support"], 2)
        self.assertEqual(ray["negative_multipliers"], 0)
        self.assertEqual(ray["verification"]["remaining_constant"], [-1, 1])
        self.assertIsNone(results["finite-parser"]["evaluation"])
        search = results["finite-parser"]["projection_search"]
        self.assertFalse(search["performed"])
        self.assertEqual(results["finite-parser"]["affine_solution_space"]["nullity"], 608)
        self.assertEqual(results["finite-parser"]["exact_equalities_rechecked"], 325)
        self.assertEqual(results["finite-parser"]["exact_equality_violations"], 0)
        self.assertIn("none is an arbitrary-width theorem", self.artifact["interpretation"])

    def test_finite_parser_farkas_certificate_cancels_exactly(self) -> None:
        certificate = self.artifact["stage_results"]["finite-parser"][
            "exact_infeasibility_certificate"
        ]
        combined = Counter()
        constant = Fraction(0)
        for inequality in certificate["inequalities"]:
            multiplier = Fraction(*inequality["multiplier"])
            self.assertGreaterEqual(multiplier, 0)
            constant += multiplier * Fraction(*inequality["constant"])
            for index, numerator, denominator in inequality["normal"]:
                combined[index] += multiplier * Fraction(numerator, denominator)
        self.assertFalse(Counter({index: value for index, value in combined.items() if value}))
        self.assertEqual(constant, Fraction(-1))
        self.assertEqual(certificate["verification"]["contradiction"], "-1 >= 0")

    def test_exact_infeasibility_certificate_recomputes_independently(self) -> None:
        certificate = self.artifact["stage_results"]["adjacent-bigrams"][
            "exact_infeasibility_certificate"
        ]
        constraint = certificate["constraint"]
        normal = Counter(
            {
                name: Fraction(numerator, denominator)
                for name, numerator, denominator in constraint["normal"]
            }
        )

        def state(record, width):
            return FrontierState(
                width,
                record["row"],
                int(record["previous_mask"], 2),
                tuple(record["partition"]),
                0,
                0,
            )

        width = constraint["width"]
        incoming = state(constraint["incoming"], width)
        outgoing = state(constraint["outgoing"], width)
        mask = int(constraint["mask"], 2)
        actual = advance_row(incoming, mask)
        self.assertIsNotNone(actual)
        self.assertEqual(structural_key(actual), structural_key(outgoing))
        direct_normal = Counter(structural_terms(outgoing, "adjacent-bigrams"))
        direct_normal.subtract(structural_terms(incoming, "adjacent-bigrams"))
        direct_normal = Counter({name: Fraction(value) for name, value in direct_normal.items() if value})
        self.assertEqual(direct_normal, normal)
        self.assertEqual(Fraction(*constraint["offset"]), _edge_weight(incoming, mask, outgoing))

        reconstructed = Counter()
        combined_rhs = Fraction(0)
        for equation in certificate["equality_combination"]:
            multiplier = Fraction(*equation["multiplier"])
            terms = structural_terms(
                state(equation["state"], equation["width"]), "adjacent-bigrams"
            )
            for name, value in terms.items():
                reconstructed[name] += multiplier * value
            combined_rhs += multiplier * Fraction(*equation["required_potential"])
        reconstructed = Counter({name: value for name, value in reconstructed.items() if value})
        self.assertEqual(reconstructed, normal)
        remaining = Fraction(*constraint["offset"]) + combined_rhs
        self.assertEqual(remaining, Fraction(-3))
        self.assertEqual(
            Fraction(*certificate["verification"]["remaining_scalar"]), remaining
        )

    @unittest.skipUnless(os.environ.get("GRID_GRAPHS_SLOW"), "slow exact regeneration")
    def test_artifact_is_fresh(self) -> None:
        self.assertEqual(build_artifact(), self.artifact)


if __name__ == "__main__":
    unittest.main()
