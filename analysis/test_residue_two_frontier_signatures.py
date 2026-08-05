from __future__ import annotations

import itertools
import hashlib
import json
import unittest

from residue_two_frontier_signatures import (
    DEFAULT_OUTPUT,
    build_artifact,
    build_alignment_records,
    initial_ranked_state,
    ordinary_state,
    ranked_advance_row,
    replay_rows,
)
from tile_grammar import advance_row, initial_state
from open_slab_signature import OpenSlabSignature, restore_open_slab_state


class RankedFrontierTests(unittest.TestCase):
    def test_ranked_transition_matches_ordinary_frontier_exhaustively_through_n3(self) -> None:
        for n in range(2, 4):
            masks = range(1 << n)
            for rows in itertools.product(masks, repeat=n):
                ranked = initial_ranked_state(n)
                ordinary = initial_state(n)
                for mask in rows:
                    ranked_next = ranked_advance_row(ranked, mask)
                    ordinary_next = advance_row(ordinary, mask)
                    self.assertEqual(ranked_next is None, ordinary_next is None)
                    if ranked_next is None:
                        break
                    self.assertIsNotNone(ordinary_next)
                    if ordinary_next is None:
                        self.fail("ranked transition existed without ordinary transition")
                    self.assertEqual(ordinary_state(ranked_next), ordinary_next)
                    self.assertEqual(
                        ranked_next.cycle_excess,
                        ranked_next.edge_count
                        - ranked_next.introduced_vertices
                        + len(ranked_next.components),
                    )
                    ranked = ranked_next
                    ordinary = ordinary_next

    def test_known_endpoint_goldens(self) -> None:
        artifact = build_artifact()
        witnesses = artifact["claim"]["witnesses"]
        expected = {
            "n08-explicit-exact": (37, 1, [0]),
            "n11-explicit-exact": (72, 1, [1]),
            "n14-explicit-exact": (119, 1, [1]),
            "n17-affine-surplus-one": (179, 1, [1]),
            "n20-phase-front-surplus-one": (250, 1, [1]),
        }
        for identifier, (u_count, components, ranks) in expected.items():
            record = witnesses[identifier]
            self.assertEqual(record["u_count"], u_count)
            self.assertEqual(record["direct_metrics"]["components"], components)
            self.assertEqual(record["direct_metrics"]["component_cycle_ranks"], ranks)
            final = record["trace"][-1]
            self.assertEqual(final["partition"], [0])
            self.assertEqual(final["u_cost"], u_count)

    def test_committed_artifact_reproduces(self) -> None:
        committed = json.loads(DEFAULT_OUTPUT.read_text())
        self.assertEqual(committed, build_artifact())

    def test_known_alignments_are_normalized_losslessly(self) -> None:
        alignments, summaries = build_alignment_records()
        self.assertEqual(
            {key: value["radius"] for key, value in alignments.items()},
            {
                "n08-to-n11": 1,
                "n11-to-n14": 1,
                "n14-to-n17": 1,
                "n17-to-n20": 3,
            },
        )
        for identifier, alignment in alignments.items():
            self.assertEqual(len(alignment["hold_rows"]), 3)
            self.assertEqual(summaries[identifier]["comparable_rows"], alignment["target_n"] - 1)
            for record in alignment["rows"][:-1]:
                normalized = record["normalized_target"]
                self.assertIsNotNone(normalized)
                self.assertEqual(
                    len(normalized["projected_partition"]), alignment["source_n"]
                )
                signature_fields = {
                    field: normalized[field]
                    for field in OpenSlabSignature.__dataclass_fields__
                }
                restored = restore_open_slab_state(OpenSlabSignature(**signature_fields))
                target = record["target_state"]
                self.assertEqual(restored.n, alignment["target_n"])
                self.assertEqual(restored.row_index, target["row_index"])
                self.assertEqual(restored.previous_u_mask, target["previous_u_mask"])
                self.assertEqual(list(restored.partition), target["partition"])
                self.assertEqual(restored.u_cost, target["u_cost"])
                self.assertEqual(restored.cycle_excess, target["cycle_excess"])
                payloads = normalized["component_payloads"]
                self.assertEqual(
                    sum(item["vertices"] for item in payloads),
                    target["introduced_vertices"],
                )
                self.assertEqual(
                    sum(item["edges"] for item in payloads), target["edge_count"]
                )
                self.assertEqual(
                    [item["attachment_label"] for item in payloads],
                    list(range(len(payloads))),
                )
                self.assertEqual(
                    sum(item["cycle_rank"] for item in normalized["component_payloads"]),
                    normalized["cycle_excess"],
                )
            self.assertIsNone(alignment["rows"][-1]["normalized_target"])

    def test_replay_rejects_disconnected_pattern(self) -> None:
        with self.assertRaisesRegex(ValueError, "seals"):
            replay_rows(("..", ".."))

    def test_artifact_integrity_and_dependencies(self) -> None:
        artifact = build_artifact()
        self.assertEqual(artifact["schema"], "grid-graphs.residue-two-frontier-traces.v1")
        dependency_paths = {
            item["path"] for item in artifact["provenance"]["dependencies"]
        }
        self.assertEqual(
            dependency_paths,
            {
                "analysis/residue_two_frontier_signatures.py",
                "analysis/analyze_residue_constructions.py",
                "analysis/census_moving_seam_alignment.py",
                "analysis/construction_lab.py",
                "analysis/diagonal_patterns.py",
                "analysis/open_slab_signature.py",
                "analysis/residue_two_phase_front_witness.txt",
                "analysis/tile_grammar.py",
            },
        )
        identity = {"schema": artifact["schema"], "claim": artifact["claim"]}
        payload = json.dumps(
            identity,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=True,
            allow_nan=False,
        ).encode("utf-8")
        self.assertEqual(
            hashlib.sha256(payload).hexdigest(),
            artifact["integrity"]["claim_sha256"],
        )


if __name__ == "__main__":
    unittest.main()
