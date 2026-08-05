from __future__ import annotations

import json
import os
import unittest

from diagonal_patterns import residue_two_explicit_pattern
from residue_two_packet_rules import (
    DEFAULT_OUTPUT,
    build_artifact,
    replay_row_segments,
    rooted_cut_signature,
    segment_totals,
    working_component_debt,
)
from tile_grammar import advance_row, initial_state, row_mask


class ResidueTwoPacketRuleTests(unittest.TestCase):
    def test_fixed_n5_rows_replay_and_telescope_exactly(self) -> None:
        incoming = initial_state(5)
        for row in residue_two_explicit_pattern(5):
            rules, outgoing = replay_row_segments(incoming, row)
            totals = segment_totals(rules)
            direct = advance_row(incoming, row_mask(row))
            self.assertEqual(outgoing, direct)
            self.assertEqual([rule.segment_mode for rule in rules], [
                "prefix_cap", "packet", "suffix_cap"
            ])
            self.assertEqual(totals["dU"], row.count("U"))
            self.assertEqual(totals["dEdges"] - totals["dCycles"], totals["dRank"])
            self.assertEqual(totals["weight"], 3 * totals["dU"] - 2 * totals["dRank"] - 1)
            self.assertEqual(
                totals["workingDebtDelta"],
                len(set(outgoing.partition[1:]) - {outgoing.partition[0]})
                - len(set(incoming.partition[1:]) - {incoming.partition[0]}),
            )
            incoming = outgoing

    def test_cut_signature_is_rooted_local_and_debt_ignores_placeholders(self) -> None:
        incoming = initial_state(5)
        rules, _ = replay_row_segments(incoming, ".UUU.")
        before = rules[0].cut_signature_before
        self.assertEqual(before, ((None,) * 6, (None,) * 6))
        for rule in rules:
            for signature in (rule.cut_signature_before, rule.cut_signature_after):
                self.assertEqual(tuple(sorted(set(
                    label for window in signature for label in window if label is not None
                ))), tuple(range(len(set(
                    label for window in signature for label in window if label is not None
                )))))

        # Public behavior of the explicitly documented private-state semantics.
        from tile_grammar import _initial_partial_row
        partial = _initial_partial_row(incoming)
        self.assertEqual(working_component_debt(incoming, partial), 0)
        self.assertEqual(rooted_cut_signature(incoming, partial), before)

    def test_committed_census_has_complete_ledgers_and_coverage_partition(self) -> None:
        artifact = json.loads(DEFAULT_OUTPUT.read_text())
        self.assertEqual(artifact["scope"]["complete_equality_corridors"], [5, 8])
        catalog = artifact["rule_catalog"]
        for width, expected_edges, expected_segments_per_edge in (("5", 220, 3), ("8", 368, 4)):
            corridor = artifact["corridors"][width]
            self.assertEqual(corridor["edges"], expected_edges)
            self.assertEqual(len(corridor["edge_ledger"]), corridor["edges"])
            self.assertEqual(corridor["segments"], corridor["edges"] * expected_segments_per_edge)
            for edge in corridor["edge_ledger"]:
                self.assertEqual(len(edge["rule_ids"]), expected_segments_per_edge)
                self.assertTrue(set(edge["rule_ids"]) <= set(catalog))
                totals = edge["totals"]
                fields = {
                    "dU": "d_u",
                    "dEdges": "d_edges",
                    "dCycles": "d_cycles",
                    "dRank": "d_rank",
                    "workingDebtDelta": "working_debt_delta",
                }
                for total, field in fields.items():
                    self.assertEqual(
                        totals[total],
                        sum(catalog[identifier][field] for identifier in edge["rule_ids"]),
                    )
                self.assertEqual(totals["dRank"], totals["dEdges"] - totals["dCycles"])
                self.assertEqual(totals["weight"], 3 * totals["dU"] - 2 * totals["dRank"] - 1)

        comparison = artifact["support_comparison"]
        self.assertEqual(
            comparison["shared_rules"] + comparison["n5_only_rules"],
            comparison["n5_rules"],
        )
        self.assertEqual(
            comparison["shared_rules"] + comparison["n8_only_rules"],
            comparison["n8_rules"],
        )
        for width, rows, segments_per_row in (("11", 11, 5), ("14", 14, 6), ("17", 17, 7)):
            trace = artifact["fixed_traces"][width]
            self.assertEqual((trace["rows"], trace["segments"]), (rows, rows * segments_per_row))
            self.assertEqual(
                trace["covered_occurrences"] + trace["uncovered_occurrences"],
                trace["segments"],
            )
            self.assertTrue(set(trace["uncovered_rule_ids"]) <= set(catalog))

    @unittest.skipUnless(os.environ.get("GRID_GRAPHS_SLOW"), "slow exact regeneration")
    def test_committed_artifact_regenerates_exactly(self) -> None:
        self.assertEqual(build_artifact(), json.loads(DEFAULT_OUTPUT.read_text()))


if __name__ == "__main__":
    unittest.main()
