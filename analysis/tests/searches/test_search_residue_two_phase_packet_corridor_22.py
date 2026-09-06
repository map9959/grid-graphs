from __future__ import annotations

import json
import unittest
from dataclasses import asdict

from analysis.searches.search_residue_two_phase_packet_corridor_22 import (
    DEFAULT_CERTIFICATE,
    LOWER_DEFECT_PACKETS,
    MUTABLE_PACKETS,
    PHASE_PATH_PACKETS,
    corridor_after_row17,
    differing_packets,
    fixed_u,
    frontier_sha256,
    phase_rows,
    provenance,
    scope,
    validate_scope,
)
from analysis.tests._support import migrated_artifact, slow_test


class PhasePacketCorridor22Tests(unittest.TestCase):
    def test_scope_covers_phase_path_and_complete_lower_defect(self) -> None:
        rows = phase_rows()
        validate_scope(rows)
        self.assertEqual(len(MUTABLE_PACKETS), 22)
        self.assertEqual(MUTABLE_PACKETS[:10], PHASE_PATH_PACKETS)
        self.assertEqual(MUTABLE_PACKETS[10:], LOWER_DEFECT_PACKETS)
        self.assertTrue(set(differing_packets(rows)).issubset(MUTABLE_PACKETS))
        self.assertEqual(fixed_u(rows), 198)
        self.assertEqual(scope(rows)["required_h_packets_primary"], 7)

    def test_committed_exact_result_is_valid(self) -> None:
        record = migrated_artifact(json.loads(DEFAULT_CERTIFICATE.read_text()))
        self.assertTrue(record["exact"])
        rows = phase_rows()
        self.assertEqual(record["provenance"], provenance(rows))
        self.assertEqual(record["result"], "negative")
        self.assertEqual(record["fixed_cap"]["rows"][0]["outgoing_states"], 40)
        self.assertEqual(record["fixed_cap"]["rows"][1]["outgoing_states"], 0)
        self.assertEqual(
            [item["rows"][0]["outgoing_states"] for item in record["alternate_caps"]],
            [307, 992, 1750],
        )
        self.assertTrue(
            all(item["rows"][1]["outgoing_states"] == 0 for item in record["alternate_caps"])
        )

    @slow_test
    def test_committed_exact_result_matches_fresh_frontier(self) -> None:
        record = migrated_artifact(json.loads(DEFAULT_CERTIFICATE.read_text()))
        rows = phase_rows()
        layer, stats = corridor_after_row17(rows, report=False)
        fresh_rows = migrated_artifact(json.loads(json.dumps([asdict(item) for item in stats])))
        self.assertEqual(record["completed_rows"], fresh_rows)
        self.assertEqual(record["corridor_after_row17"]["states"], len(layer))
        self.assertEqual(
            record["corridor_after_row17"]["assignments"],
            sum(node.ways for node in layer.values()),
        )
        self.assertEqual(record["corridor_after_row17"]["frontier_sha256"], frontier_sha256(layer))


if __name__ == "__main__":
    unittest.main()
