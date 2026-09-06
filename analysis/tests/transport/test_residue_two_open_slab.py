from __future__ import annotations

import json
import unittest

from analysis.residue_certificates.residue_two_frontier_signatures import replay_rows
from analysis.transport.residue_two_open_slab_census import (
    CHANNELS,
    DEFAULT_OUTPUT,
    RootedOpenSlabSignature,
    build_artifact,
    pattern_inputs,
    removed_prefix_cost,
)
from analysis.tests._support import migrated_artifact


class RootedOpenSlabCensusTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.fresh = build_artifact()

    def test_committed_certificate_reproduces(self) -> None:
        self.assertEqual(migrated_artifact(json.loads(DEFAULT_OUTPUT.read_text())), self.fresh)

    def test_signature_retains_root_and_exact_charge(self) -> None:
        rows = pattern_inputs()["B20"]
        state = replay_rows(rows)[8]
        removed = removed_prefix_cost(rows, 8, 4)
        signature = RootedOpenSlabSignature.extract(state, 4, removed)
        self.assertEqual(signature.projected_partition[0], 0)
        self.assertEqual(signature.normalized_u_cost, state.u_cost - removed)
        self.assertEqual(len(signature.attachment_partition) - len(set(signature.projected_partition)), 3)

    def test_census_is_complete_and_any_hit_is_exact(self) -> None:
        for pair in self.fresh["claim"]["pairs"]:
            if not pair["searched"]:
                continue
            source_orientations, target_orientations = pair["orientation_counts"]
            expected = (
                source_orientations
                * target_orientations
                * (pair["source_n"] - 1)
                * (pair["target_n"] - 1)
                * (pair["target_n"] - 3)
            )
            self.assertEqual(pair["candidates_tested"], expected)
            self.assertEqual(
                pair["exact_compatible_count"], len(pair["exact_compatible"])
            )
            for hit in pair["exact_compatible"]:
                self.assertEqual(tuple(hit["mismatch"]), CHANNELS)
                self.assertFalse(any(hit["mismatch"].values()))

    def test_exact_charge_cuts_miss_by_one_hidden_component(self) -> None:
        searched = [pair for pair in self.fresh["claim"]["pairs"] if pair["searched"]]
        self.assertEqual(
            [(pair["id"], pair["candidates_tested"]) for pair in searched],
            [("A17-to-B20", 330752), ("B20-to-A23", 535040)],
        )
        for pair in searched:
            self.assertEqual(pair["exact_compatible_count"], 0)
            self.assertGreater(pair["exact_charge_candidate_count"], 0)
            self.assertEqual(
                pair["minimum_topology_mismatch_at_exact_charge"],
                {"mask": 0, "partition": 0, "closed": 1, "cycle": 0},
            )

        self_family = next(
            pair for pair in self.fresh["claim"]["pairs"] if pair["id"] == "A17-to-affine20"
        )
        self.assertEqual(self_family["minimum_charge_mismatch"], 1)


if __name__ == "__main__":
    unittest.main()
