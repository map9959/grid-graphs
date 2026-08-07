from __future__ import annotations

import json
import os
import unittest
from fractions import Fraction

from equality_corridor import build_equality_corridor
from residue_two_attachment_skeleton import linear_frontier_metric
from residue_two_obligation5_potential import (
    DEFAULT_OUTPUT,
    _rref_solve,
    build_artifact,
    verify_symbolic,
)
from tile_grammar import advance_row


class ResidueTwoObligation5PotentialTests(unittest.TestCase):
    def test_exact_solver_handles_rationals_and_infeasibility(self) -> None:
        solution, diagnostics = _rref_solve(
            [[Fraction(2), Fraction(1)], [Fraction(1), Fraction(-1)]],
            [Fraction(1), Fraction(0)],
        )
        self.assertEqual(solution, [Fraction(1, 3), Fraction(1, 3)])
        self.assertEqual(diagnostics["rank"], 2)
        impossible, diagnostics = _rref_solve(
            [[Fraction(1)], [Fraction(1)]], [Fraction(0), Fraction(1)]
        )
        self.assertIsNone(impossible)
        self.assertTrue(diagnostics["conflicts"])

    def test_cegar_formula_has_exact_symbolic_certificate(self) -> None:
        artifact = json.loads(DEFAULT_OUTPUT.read_text())
        transcript = artifact["cegar"]
        self.assertFalse(transcript[0]["feasible"])
        self.assertFalse(transcript[1]["feasible"])
        self.assertTrue(transcript[-1]["feasible"])
        self.assertEqual(transcript[-1]["stage"], "out_rooted_debt")
        names = tuple(transcript[-1]["terms"])
        stored = artifact["potential"]["coefficients"]
        coefficients = [Fraction(*stored.get(name, [0, 1])) for name in names]
        result = verify_symbolic(names, coefficients)
        self.assertEqual(result["rules"], 19)
        self.assertTrue(result["coefficientwise_verified"])
        self.assertEqual(result["negative_slope_rules"], 0)
        self.assertTrue(result["all_rules_are_zero_slack_identities"])

    def test_committed_artifact_is_width_independent_accounting_only(self) -> None:
        artifact = json.loads(DEFAULT_OUTPUT.read_text())
        self.assertTrue(artifact["scope"]["arbitrary_packet_length_certificate"])
        self.assertFalse(artifact["scope"]["low_curvature_language_coverage_claimed"])
        self.assertFalse(artifact["scope"]["lower_bound_claimed"])
        self.assertEqual(artifact["potential"]["transition_identity"], "weight + Phi(out) - Phi(in) = 0")
        self.assertEqual(artifact["terminal_accounting_identity"]["connected_terminal_value"], "Phi=-K(U)")
        self.assertNotIn("lookup", artifact["potential"]["formula"])
        self.assertIn("unoccupied packets", artifact["potential"]["silent_carrier_policy"])
        for k in range(1, 20):
            n = 3 * k + 2
            u = 6 * k * k + 5 * k + 3
            self.assertEqual(-3 * u + 2 * (n - 1) ** 2 + n, -5)

    def test_terminal_formula_is_negative_curvature_for_arbitrary_u(self) -> None:
        for n in range(2, 20):
            for u in (0, n, n * n):
                curvature = 3 * u - 2 * (n - 1) ** 2 - n
                phi = -3 * u + 2 * (n - 1) ** 2 + n
                self.assertEqual(phi, -curvature)

    def test_formula_is_exact_accounting_on_all_small_accepted_edges(self) -> None:
        def phi(state) -> int:
            faces = min(state.row_index, state.n - 1) * (state.n - 1)
            debt = linear_frontier_metric(state.partition)["attachment_debt"]
            return -3 * state.u_cost + state.row_index + 2 * faces - 2 * debt

        checked = 0
        for n in range(2, 6):
            corridor = build_equality_corridor(n)
            for row in range(n):
                for incoming in corridor.layers[row].values():
                    for mask in range(1 << n):
                        outgoing = advance_row(incoming, mask)
                        if outgoing is None:
                            continue
                        rank_in = min(row, n - 1) * (n - 1) - linear_frontier_metric(
                            incoming.partition
                        )["attachment_debt"]
                        rank_out = min(row + 1, n - 1) * (n - 1) - linear_frontier_metric(
                            outgoing.partition
                        )["attachment_debt"]
                        weight = 3 * mask.bit_count() - 2 * (rank_out - rank_in) - 1
                        self.assertEqual(weight + phi(outgoing) - phi(incoming), 0)
                        checked += 1
        self.assertEqual(checked, 3567)

    @unittest.skipUnless(os.environ.get("GRID_GRAPHS_SLOW"), "slow exact regeneration")
    def test_artifact_regenerates_exactly(self) -> None:
        self.assertEqual(build_artifact(), json.loads(DEFAULT_OUTPUT.read_text()))


if __name__ == "__main__":
    unittest.main()
