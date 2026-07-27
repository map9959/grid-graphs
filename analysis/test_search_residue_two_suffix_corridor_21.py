from __future__ import annotations

import json
import unittest

from search_residue_two_suffix_corridor import layer_after_row17, packet_domains
from search_residue_two_suffix_corridor_21 import (
    DEFAULT_CERTIFICATE,
    DISTRIBUTIONS,
    FIXED_U,
    MUTABLE_PACKET_COLUMNS,
    REQUIRED_H_PACKETS,
    alternate_cap_search,
    fixed_cap_search,
    frontier_sha256,
    provenance,
)


class SuffixCorridor21Tests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.layer, cls.stats = layer_after_row17(
            report=False,
            mutable_packet_columns=MUTABLE_PACKET_COLUMNS,
        )

    def test_scope_is_exactly_twenty_one_packets(self) -> None:
        mutable = []
        for row in range(11, 18):
            domains = packet_domains(
                row, mutable_packet_columns=MUTABLE_PACKET_COLUMNS
            )
            mutable.extend(
                (row, column)
                for column, domain in enumerate(domains)
                if len(domain) > 1
            )
        self.assertEqual(
            mutable,
            [(row, column) for row in range(11, 18) for column in range(3)],
        )
        self.assertEqual(FIXED_U, 201)
        self.assertEqual(REQUIRED_H_PACKETS, 6)

    def test_exact_corridor_counts_and_hash_are_stable(self) -> None:
        self.assertEqual(
            [stats.outgoing_states for stats in self.stats],
            [5, 83, 485, 787, 481, 129, 4],
        )
        self.assertEqual(
            [stats.assignments_represented for stats in self.stats],
            [5, 89, 793, 2782, 2372, 435, 6],
        )
        self.assertEqual(
            frontier_sha256(self.layer),
            "346ec214faec1d377b929f6f0689daf390e3504d4a69e54b6c0357a9b22234d7",
        )

    def test_fixed_and_alternate_caps_are_exact_negative(self) -> None:
        fixed, witness = fixed_cap_search(self.layer)
        self.assertIsNone(witness)
        self.assertEqual(fixed["result"], "negative")
        self.assertEqual(
            [row["outgoing_states"] for row in fixed["rows"]], [4, 0]
        )

        caps, witness = alternate_cap_search(self.layer, report=False)
        self.assertIsNone(witness)
        self.assertEqual(
            [(cap.row18_u, cap.row19_u) for cap in caps], list(DISTRIBUTIONS)
        )
        self.assertEqual([cap.row18_states for cap in caps], [32, 104, 180])
        self.assertEqual([cap.row18_assignments for cap in caps], [48, 156, 270])
        self.assertTrue(all(cap.row19_states == 0 for cap in caps))

    def test_committed_result_records_exact_scope(self) -> None:
        record = json.loads(DEFAULT_CERTIFICATE.read_text())
        self.assertTrue(record["exact"])
        self.assertEqual(record["result"], "negative")
        self.assertEqual(record["scope"]["mutable_packets"], 21)
        self.assertEqual(record["provenance"], provenance())
        self.assertEqual(record["corridor_after_row17"]["states"], len(self.layer))
        self.assertEqual(
            record["corridor_after_row17"]["frontier_sha256"],
            frontier_sha256(self.layer),
        )


if __name__ == "__main__":
    unittest.main()
