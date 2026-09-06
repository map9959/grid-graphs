from __future__ import annotations

import json
import random
import tempfile
import unittest
from fractions import Fraction
from pathlib import Path

from analysis.bounds.proof_oriented_identities import (
    DEMO_CERTIFICATE,
    CertificateError,
    InfeasiblePotentialError,
    PathTelescope,
    TileRowDeltas,
    build_complete_tile_certificate,
    build_pooled_frontier_feature_experiment,
    check_n17_178_identity,
    check_pattern_identities,
    check_residue_two_terminal_algebra,
    export_complete_tile_row_source,
    reverify_complete_tile_certificate,
    synthesize_difference_potentials,
    tile_grammar_row_deltas,
    tile_grammar_transition_record,
    transition_slack,
    verify_frontier_certificate,
    verify_path_telescope,
)
from analysis.searches.certify_residue_two_relaxation import WITNESS
from analysis.tests._support import migrated_artifact
from analysis.tiles.tile_grammar import advance_row, initial_state


class PatternIdentityTests(unittest.TestCase):
    def test_parallel_boundary_edges_and_cycle_rank(self) -> None:
        result = check_pattern_identities(["UU", "UU"])
        self.assertEqual(result.dual_edges, 4)
        self.assertEqual(result.graphic_rank, 1)
        self.assertEqual(result.components, 1)
        self.assertEqual(result.cycle_rank, 3)
        self.assertEqual(result.component_excess, 0)

    def test_isolated_dual_vertex_identity(self) -> None:
        result = check_pattern_identities(["U.", ".U"])
        self.assertEqual(result.components, 2)
        self.assertEqual(result.component_excess, 1)
        self.assertEqual(result.run_sum + result.cycle_rank - result.identity_constant, 1)

    def test_n17_identity_on_deterministic_178_u_patterns(self) -> None:
        for seed in range(5):
            vertices = list(range(17 * 17))
            random.Random(seed).shuffle(vertices)
            selected = set(vertices[:178])
            pattern = [
                "".join("U" if row * 17 + column in selected else "." for column in range(17))
                for row in range(17)
            ]
            result = check_n17_178_identity(pattern)
            self.assertEqual(result.identity_constant, 100)
            self.assertEqual(result.component_excess, result.run_sum + result.cycle_rank - 100)

    def test_n17_identity_on_bundled_relaxation_pattern(self) -> None:
        result = check_n17_178_identity(WITNESS)
        self.assertEqual(result.component_excess, 1)
        self.assertEqual(result.run_sum + result.cycle_rank - 100, 1)


class FrontierCertificateTests(unittest.TestCase):
    def test_demonstrative_certificate_is_exactly_valid(self) -> None:
        certificate = migrated_artifact(json.loads(DEMO_CERTIFICATE.read_text()))
        self.assertEqual(
            verify_frontier_certificate(certificate),
            {"states": 3, "transitions": 2, "tight": 1},
        )

    def test_failed_transition_is_rejected(self) -> None:
        certificate = migrated_artifact(json.loads(DEMO_CERTIFICATE.read_text()))
        certificate["transitions"][1]["charge"] = 5
        with self.assertRaisesRegex(CertificateError, "bottom-row.*fails"):
            verify_frontier_certificate(certificate)

    def test_noncanonical_rational_is_rejected(self) -> None:
        certificate = migrated_artifact(json.loads(DEMO_CERTIFICATE.read_text()))
        certificate["states"][0]["potential"] = [0, 2]
        with self.assertRaisesRegex(CertificateError, "reduced"):
            verify_frontier_certificate(certificate)

    def test_tile_grammar_adapter_recovers_rank_deltas(self) -> None:
        start = initial_state(2)
        top = advance_row(start, 0b11)
        self.assertIsNotNone(top)
        finished = advance_row(top, 0b11)
        self.assertIsNotNone(finished)
        first = tile_grammar_transition_record("top-row", start, top, [3], "start", "top-UU", 2)
        second = tile_grammar_transition_record(
            "bottom-row", top, finished, [3], "top-UU", "finished-UU-UU", 4
        )
        self.assertEqual((first["dU"], first["dRank"], first["metadata"]["dCycles"]), (2, 1, 0))
        self.assertEqual((second["dU"], second["dRank"], second["metadata"]["dCycles"]), (2, 0, 3))
        bottom = tile_grammar_row_deltas(top, 0b11, finished)
        self.assertEqual(
            bottom,
            TileRowDeltas(
                u_count=2,
                horizontal_runs=1,
                vertical_edges=2,
                cycle_delta=3,
                edge_delta=3,
                rank_delta=0,
            ),
        )

    def test_row_curvature_identity_on_complete_sources(self) -> None:
        accepted = 0
        saw_top = saw_bottom = saw_empty = saw_cycle = False
        for n in range(2, 7):
            representatives = {(0, 0, (0,)): initial_state(n)}
            for _ in range(n):
                children = {}
                for state in representatives.values():
                    for mask in range(1 << n):
                        outgoing = advance_row(state, mask)
                        if outgoing is None:
                            continue
                        deltas = tile_grammar_row_deltas(state, mask, outgoing)
                        self.assertEqual(
                            3 * deltas.u_count - 2 * deltas.rank_delta,
                            deltas.u_count
                            + 2 * deltas.horizontal_runs
                            - 2 * deltas.vertical_edges
                            + 2 * deltas.cycle_delta,
                        )
                        accepted += 1
                        saw_top |= outgoing.row_index == 1
                        saw_bottom |= outgoing.row_index == n
                        saw_empty |= mask == 0
                        saw_cycle |= deltas.cycle_delta > 0
                        key = (
                            outgoing.row_index,
                            outgoing.previous_u_mask,
                            outgoing.partition,
                        )
                        children.setdefault(key, outgoing)
                representatives = children
        self.assertEqual(accepted, 19_948)
        self.assertTrue(all((saw_top, saw_bottom, saw_empty, saw_cycle)))


class TransitionTelescopeTests(unittest.TestCase):
    def setUp(self) -> None:
        self.potentials = {
            "a": Fraction(1, 3),
            "b": Fraction(4, 3),
            "c": Fraction(5, 3),
        }
        self.tight = {
            "id": "ab",
            "in": "a",
            "out": "b",
            "dU": 1,
            "dRank": 1,
            "charge": 0,
        }
        self.positive = {
            "id": "bc",
            "in": "b",
            "out": "c",
            "dU": 1,
            "dRank": 0,
            "charge": 1,
        }

    def test_exact_transition_slack_is_tight(self) -> None:
        self.assertEqual(transition_slack(self.tight, self.potentials), Fraction(0))

    def test_positive_slack_path_telescopes(self) -> None:
        result = verify_path_telescope([self.tight, self.positive], self.potentials)
        self.assertEqual(
            result,
            PathTelescope(
                initial_state="a",
                terminal_state="c",
                initial_potential=Fraction(1, 3),
                terminal_potential=Fraction(5, 3),
                total_u=2,
                total_rank=1,
                total_charge=1,
                total_slack=Fraction(5, 3),
            ),
        )
        self.assertEqual(result.transition_total, Fraction(4))
        self.assertEqual(result.telescoped_total, Fraction(4))

    def test_malformed_path_and_unknown_state_are_rejected(self) -> None:
        disconnected = {**self.positive, "in": "a"}
        with self.assertRaisesRegex(CertificateError, "not contiguous"):
            verify_path_telescope([self.tight, disconnected], self.potentials)
        unknown = {**self.tight, "out": "missing"}
        with self.assertRaisesRegex(CertificateError, "unknown state"):
            transition_slack(unknown, self.potentials)

    def test_residue_two_terminal_algebra(self) -> None:
        self.assertEqual(check_residue_two_terminal_algebra(2), 3)
        self.assertEqual(check_residue_two_terminal_algebra(5), 14)
        self.assertEqual(check_residue_two_terminal_algebra(17, Fraction(5)), 178)
        with self.assertRaisesRegex(ValueError, r"3k\+2"):
            check_residue_two_terminal_algebra(6)
        with self.assertRaisesRegex(ValueError, "constant 5"):
            check_residue_two_terminal_algebra(17, Fraction(4))


class CompleteSmallSourceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.certificate = build_complete_tile_certificate(3, 0)

    def test_export_exhausts_declared_reachable_n3_source(self) -> None:
        source = export_complete_tile_row_source(3, 0)
        self.assertEqual(source["reachable_states_by_row"], [1, 8, 14, 8])
        self.assertEqual(source["attempted"], (1 + 8 + 14) * 8)
        self.assertEqual((source["accepted"], source["rejected"]), (84, 100))
        self.assertEqual(len(source["states"]), 31)
        outgoing_counts: dict[str, int] = {}
        for transition in source["transitions"]:
            outgoing_counts[transition["in"]] = outgoing_counts.get(transition["in"], 0) + 1
        nonterminal = [
            state for state in source["states"] if state["metadata"]["row_index"] < 3
        ]
        self.assertEqual(len(nonterminal), 23)
        self.assertTrue(all(0 < outgoing_counts[state["id"]] <= 8 for state in nonterminal))

    def test_emitted_json_is_independently_regenerated_and_reverified(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "n3-certificate.json"
            path.write_text(json.dumps(self.certificate, indent=2) + "\n")
            loaded = migrated_artifact(json.loads(path.read_text()))
            self.assertEqual(
                reverify_complete_tile_certificate(loaded),
                {"states": 31, "transitions": 84, "tight": 50},
            )

    def test_source_reverification_rejects_even_inequality_valid_tampering(self) -> None:
        certificate = migrated_artifact(json.loads(json.dumps(self.certificate)))
        certificate["transitions"][0]["charge"] = -1
        verify_frontier_certificate(certificate)
        with self.assertRaisesRegex(CertificateError, "differs from regenerated"):
            reverify_complete_tile_certificate(certificate)

    def test_zero_charge_tight_analysis_and_terminal_bound(self) -> None:
        analysis = self.certificate["analysis"]
        self.assertEqual(analysis["minimum_terminal_potential"], [7, 1])
        self.assertEqual(analysis["maximum_terminal_potential"], [10, 1])
        self.assertEqual(analysis["implied_u_lower_bound"], 5)
        self.assertEqual(analysis["tight_transitions"], 50)
        self.assertEqual(
            analysis["tight_transitions_by_destination_row"],
            {"1": 8, "2": 19, "3": 23},
        )
        witness = check_pattern_identities(analysis["tight_witness_rows"])
        self.assertEqual((witness.u_count, witness.graphic_rank, witness.components), (5, 4, 1))
        self.assertIn("sharp for this finite source", analysis["zero_charge_assessment"])

    def test_complete_sources_through_n6_reproduce_known_minima(self) -> None:
        expected = {
            2: (9, 13, 8, 2),
            4: (106, 504, 162, 8),
            5: (369, 2966, 690, 14),
            6: (1264, 16381, 3058, 20),
        }
        for n, (states, transitions, tight, minimum_u) in expected.items():
            with self.subTest(n=n):
                certificate = build_complete_tile_certificate(n, 0)
                self.assertEqual(len(certificate["states"]), states)
                self.assertEqual(len(certificate["transitions"]), transitions)
                self.assertEqual(certificate["analysis"]["tight_transitions"], tight)
                self.assertEqual(certificate["analysis"]["implied_u_lower_bound"], minimum_u)
                witness = check_pattern_identities(certificate["analysis"]["tight_witness_rows"])
                self.assertEqual(witness.u_count, minimum_u)
                self.assertEqual(witness.components, 1)

    def test_difference_synthesizer_detects_negative_cycle(self) -> None:
        transitions = [
            {"id": "ab", "in": "a", "out": "b", "dU": 0, "dRank": 0, "charge": 1},
            {"id": "ba", "in": "b", "out": "a", "dU": 0, "dRank": 0, "charge": 0},
        ]
        with self.assertRaisesRegex(InfeasiblePotentialError, "negative cycle"):
            synthesize_difference_potentials(["a", "b"], transitions, "a")

    def test_coarse_pooled_features_are_feasible_but_lose_residue_two(self) -> None:
        result = build_pooled_frontier_feature_experiment(level="coarse")
        self.assertEqual(
            result["census"],
            {
                "concrete_states": 1770,
                "feature_states": 920,
                "concrete_transitions": 19935,
                "pooled_transitions": 11751,
                "tight_concrete_transitions": 3214,
            },
        )
        self.assertEqual(
            result["analysis"]["exact_width_terminal_constants"],
            {"3": 4, "4": 2, "5": 5, "6": 4},
        )
        self.assertEqual(
            result["analysis"]["pooled_phase_terminal_constants"],
            {"0": [4, 1], "1": [2, 1], "2": [2, 1]},
        )

    def test_row_runs_recover_all_three_small_residue_constants(self) -> None:
        result = build_pooled_frontier_feature_experiment(level="runs")
        self.assertEqual(result["census"]["feature_states"], 1065)
        self.assertEqual(
            result["analysis"]["pooled_phase_terminal_constants"],
            {"0": [4, 1], "1": [2, 1], "2": [5, 1]},
        )
        self.assertEqual(
            result["analysis"]["pooled_width_terminal_constants"],
            {"3": [4, 1], "4": [2, 1], "5": [5, 1], "6": [4, 1]},
        )
        for witness in result["analysis"]["exact_minimum_witness_tightness"].values():
            self.assertEqual(witness["tight_rows"], witness["rows"])
            self.assertEqual(witness["total_slack"], [0, 1])


if __name__ == "__main__":
    unittest.main()
