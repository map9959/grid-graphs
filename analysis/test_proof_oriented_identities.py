from __future__ import annotations

import json
import random
import tempfile
import unittest
from pathlib import Path

from certify_residue_two_relaxation import WITNESS
from proof_oriented_identities import (
    CertificateError,
    DEMO_CERTIFICATE,
    InfeasiblePotentialError,
    build_complete_tile_certificate,
    check_n17_178_identity,
    check_pattern_identities,
    export_complete_tile_row_source,
    reverify_complete_tile_certificate,
    synthesize_difference_potentials,
    tile_grammar_transition_record,
    verify_frontier_certificate,
)
from tile_grammar import advance_row, initial_state


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
        certificate = json.loads(DEMO_CERTIFICATE.read_text())
        self.assertEqual(
            verify_frontier_certificate(certificate),
            {"states": 3, "transitions": 2, "tight": 1},
        )

    def test_failed_transition_is_rejected(self) -> None:
        certificate = json.loads(DEMO_CERTIFICATE.read_text())
        certificate["transitions"][1]["charge"] = 5
        with self.assertRaisesRegex(CertificateError, "bottom-row.*fails"):
            verify_frontier_certificate(certificate)

    def test_noncanonical_rational_is_rejected(self) -> None:
        certificate = json.loads(DEMO_CERTIFICATE.read_text())
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
            loaded = json.loads(path.read_text())
            self.assertEqual(
                reverify_complete_tile_certificate(loaded),
                {"states": 31, "transitions": 84, "tight": 50},
            )

    def test_source_reverification_rejects_even_inequality_valid_tampering(self) -> None:
        certificate = json.loads(json.dumps(self.certificate))
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


if __name__ == "__main__":
    unittest.main()
