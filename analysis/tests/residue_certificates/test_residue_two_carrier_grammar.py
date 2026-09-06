from __future__ import annotations

import json
import os
import unittest


from analysis.residue_certificates.residue_two_carrier_grammar import (
    CarrierEvent,
    CarrierRecord,
    ComponentEvent,
    build_artifact,
    expand_carrier_record,
    packet_groups,
    recognize_partition,
)
from analysis._paths import analysis_path
from analysis.tests._support import migrated_artifact


ARTIFACT = analysis_path("residue_two_carrier_grammar.json")


class ResidueTwoCarrierGrammarTests(unittest.TestCase):
    def test_exact_packet_groups(self) -> None:
        self.assertEqual(packet_groups(5), ((0,), (1, 2, 3)))
        self.assertEqual(packet_groups(8), ((0,), (1, 2, 3), (4, 5, 6)))
        with self.assertRaises(ValueError):
            packet_groups(7)

    def test_acceptance_and_lossless_round_trip(self) -> None:
        partition = (9, 4, 4, 7, 7, 9, 4, 9)
        result = recognize_partition(8, partition)
        self.assertTrue(result.accepted)
        self.assertEqual(expand_carrier_record(result.record), (0, 1, 1, 2, 2, 0, 1, 0))
        self.assertEqual(result.record.carriers, (CarrierEvent(0, 1), CarrierEvent(1, 1)))

    def test_detailed_rejection_reasons(self) -> None:
        hole = recognize_partition(8, (0, 1, 0, 0, 0, 1, 0, 0))
        self.assertFalse(hole.accepted)
        self.assertEqual(hole.support_holes[0].missing_groups, (1,))
        concurrent = recognize_partition(8, (0, 0, 1, 2, 0, 1, 2, 0))
        self.assertFalse(concurrent.accepted)
        self.assertEqual(concurrent.concurrent_carriers[0].components, (1, 2))

    def test_record_validation_is_exact(self) -> None:
        broken = CarrierRecord(
            5,
            4,
            (ComponentEvent(1, 0, (0,), "single"),),
            (CarrierEvent(0, 1),),
        )
        with self.assertRaises(ValueError):
            expand_carrier_record(broken)

    def test_cached_artifact_declares_scope_and_key_counts(self) -> None:
        artifact = migrated_artifact(json.loads(ARTIFACT.read_text()))
        self.assertFalse(artifact["scope"]["zero_slack_coverage_proof"])
        self.assertEqual(artifact["scope"]["complete_equality_corridors"], [5, 8])
        self.assertEqual(artifact["scope"]["fixed_equality_traces"], [11, 14])
        self.assertEqual(artifact["scope"]["near_equality_control"], {"width": 17, "u_count": 179})
        self.assertEqual(artifact["sources"]["n5-complete-equality-corridor"]["states"], 117)
        self.assertEqual(artifact["sources"]["n8-complete-equality-corridor"]["states"], 208)
        self.assertEqual(artifact["sources"]["n5-full-structurally-reachable-layers"]["states"], 369)
        self.assertEqual(artifact["sources"]["n8-full-structurally-reachable-layers"]["states"], 14582)
        self.assertEqual(
            (
                artifact["sources"]["n8-full-structurally-reachable-layers"]["accepted"],
                artifact["sources"]["n8-full-structurally-reachable-layers"]["excluded"],
                artifact["sources"]["n8-full-structurally-reachable-layers"]["states_with_support_holes"],
                artifact["sources"]["n8-full-structurally-reachable-layers"]["states_with_concurrent_carriers"],
            ),
            (14465, 117, 101, 16),
        )
        for name, count in (
            ("n11-fixed-equality-trace", 12),
            ("n14-fixed-equality-trace", 15),
            ("n17-fixed-near-equality-179-U-trace", 18),
        ):
            self.assertEqual((artifact["sources"][name]["accepted"], artifact["sources"][name]["excluded"]), (count, 0))
        for source in artifact["sources"].values():
            self.assertEqual(source["lossless_round_trips"], source["states"])
            self.assertEqual(source["accepted"] + source["excluded"], source["states"])
        for transition in artifact["row_transitions"].values():
            self.assertEqual(
                transition["staying_in_grammar"] + transition["leaving_grammar"],
                transition["frontier_accepted_transitions"],
            )
            self.assertEqual(
                transition["exact_equality_corridor_edges"],
                transition["total_equality_corridor_edges"],
            )
        self.assertEqual(
            tuple(artifact["row_transitions"]["5"][field] for field in ("frontier_accepted_transitions", "staying_in_grammar", "leaving_grammar", "exact_equality_corridor_edges")),
            (2966, 2966, 0, 220),
        )
        self.assertEqual(
            tuple(artifact["row_transitions"]["8"][field] for field in ("frontier_accepted_transitions", "staying_in_grammar", "leaving_grammar", "exact_equality_corridor_edges")),
            (461145, 460703, 442, 368),
        )

    @unittest.skipUnless(os.environ.get("GRID_GRAPHS_SLOW"), "slow exact regeneration")
    def test_cached_artifact_regenerates_exactly(self) -> None:
        self.assertEqual(build_artifact(), migrated_artifact(json.loads(ARTIFACT.read_text())))


if __name__ == "__main__":
    unittest.main()
