from __future__ import annotations

import json
import os
import unittest


from analysis.transport.equality_corridor import build_equality_corridor
from analysis.residue_certificates.residue_two_equality_cegar import observe_corridor
from analysis.residue_certificates.residue_two_packet_cegar import (
    LEVELS,
    WIDTH_DEPENDENT_FIELDS,
    build_artifact,
    packet_carry_signatures,
    packet_global_carry,
    packet_local_restrictions,
    packet_signature,
    packet_words,
)
from analysis._paths import analysis_path
from analysis.tests._support import migrated_artifact


ARTIFACT = analysis_path("residue_two_packet_cegar.json")


class ResidueTwoPacketCegarTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.observations = observe_corridor(build_equality_corridor(5))

    def test_ordered_interior_packet_words_and_rooted_restrictions(self) -> None:
        observed = next(item for item in self.observations if item.state.previous_u_mask)
        state = observed.state
        self.assertEqual(packet_words(state), ((state.previous_u_mask >> 1) & 7,))
        self.assertEqual(len(packet_local_restrictions(state)), 1)
        self.assertEqual(len(packet_carry_signatures(state)), 2)
        left_face, rooted_packets = packet_global_carry(state)
        self.assertEqual(len(rooted_packets), 1)
        self.assertEqual(
            (left_face, *rooted_packets[0]),
            tuple(state.partition[1:]),
        )
        with self.assertRaises(ValueError):
            packet_words(state.__class__(4, state.row_index, state.previous_u_mask,
                                         state.partition, state.u_cost,
                                         state.cycle_excess))

    def test_hierarchy_refines_and_marks_position_fields_width_dependent(self) -> None:
        for observed in self.observations:
            words = packet_signature(observed.state, "packet_words")
            local = packet_signature(observed.state, "packet_local")
            carry = packet_signature(observed.state, "packet_carry")
            positioned = packet_signature(observed.state, "packet_carry_positioned")
            self.assertEqual(local[:-1], words)
            self.assertEqual(carry[:-1], local)
            self.assertEqual(positioned[:-2], carry)
        self.assertEqual(
            WIDTH_DEPENDENT_FIELDS["packet_carry"],
            ("ordered_packet_sequence_length",),
        )
        self.assertEqual(
            WIDTH_DEPENDENT_FIELDS["packet_carry_positioned"],
            ("ordered_packet_sequence_length", "absolute_row", "rows_to_bottom"),
        )
        with self.assertRaises(ValueError):
            packet_signature(self.observations[0].state, "unknown")

    def test_cached_complete_corridor_audit_and_collision_counts(self) -> None:
        artifact = migrated_artifact(json.loads(ARTIFACT.read_text()))
        self.assertEqual(artifact["definitions"]["hierarchy"], list(LEVELS))
        self.assertEqual(artifact["corridors"]["5"]["packets"], 1)
        self.assertEqual(artifact["corridors"]["8"]["packets"], 2)
        self.assertEqual(artifact["observations"], {
            "outgoing_equality_transitions": 588,
            "states": 325,
        })
        expected = {
            "packet_words": (168, 55, 53, 45, 8, 0, 0),
            "packet_local": (306, 16, 14, 12, 2, 0, 0),
            "packet_carry": (325, 0, 0, 0, 0, 0, 0),
            "packet_global_carry": (325, 0, 0, 0, 0, 0, 0),
            "packet_carry_positioned": (325, 0, 0, 0, 0, 0, 0),
            "rooted_packet_control": (325, 0, 0, 0, 0, 0, 0),
        }
        for level, counts in expected.items():
            report = artifact["hierarchy"][level]
            kinds = report["collision_groups_by_kind"]
            self.assertEqual(
                (
                    report["keys"],
                    report["merged_groups"],
                    report["collision_groups"],
                    kinds["within_width_bulk"],
                    kinds["within_width_cap"],
                    kinds["cross_width_bulk"],
                    kinds["cross_width_cap"],
                ),
                counts,
            )
        self.assertEqual(artifact["smallest_tested_zero_within_width_bulk"], "packet_carry")
        self.assertEqual(artifact["first_lossless_packet_level"], "packet_global_carry")
        selected = artifact["smallest_tested_zero_within_width_bulk"]
        self.assertEqual(
            artifact["hierarchy"][selected]["collision_groups_by_kind"]["within_width_bulk"],
            0,
        )
        self.assertEqual(artifact["hierarchy"]["rooted_packet_control"]["collision_groups"], 0)
        for report in artifact["hierarchy"].values():
            self.assertEqual(
                set(report["collision_groups_by_kind"]),
                {"within_width_bulk", "within_width_cap", "cross_width_bulk", "cross_width_cap"},
            )

    @unittest.skipUnless(os.environ.get("GRID_GRAPHS_SLOW"), "slow exact regeneration")
    def test_cached_artifact_regenerates_exactly(self) -> None:
        self.assertEqual(build_artifact(), migrated_artifact(json.loads(ARTIFACT.read_text())))


if __name__ == "__main__":
    unittest.main()
