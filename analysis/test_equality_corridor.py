from __future__ import annotations

import json
import os
import unittest
from dataclasses import replace
from itertools import product
from pathlib import Path

from equality_corridor import (
    _edge,
    build_equality_corridor,
    residue_two_comparison,
    structural_key,
)
from proof_oriented_identities import tile_grammar_row_deltas
from tile_grammar import advance_row, initial_state


class EqualityCorridorTests(unittest.TestCase):
    def test_exact_corridors_through_n6(self) -> None:
        expected = {
            3: (4, 5, [1, 7, 10, 7], [7, 15, 18], 24),
            4: (2, 8, [1, 4, 4, 5, 4], [4, 4, 14, 5], 14),
            5: (5, 14, [1, 19, 26, 28, 24, 19], [19, 26, 60, 78, 37], 242),
            6: (4, 20, [1, 8, 8, 7, 14, 10, 8], [8, 8, 14, 16, 38, 10], 96),
        }
        for n, (weight, u_count, states, edges, paths) in expected.items():
            with self.subTest(n=n):
                corridor = build_equality_corridor(n)
                self.assertEqual(corridor.minimum_weight, weight)
                self.assertEqual(corridor.minimum_u, u_count)
                self.assertEqual([len(layer) for layer in corridor.corridor_states], states)
                self.assertEqual([len(layer) for layer in corridor.corridor_edges], edges)
                self.assertEqual(corridor.minimum_path_count, paths)

    def test_n2_path_count_matches_direct_mask_enumeration(self) -> None:
        weights = []
        for masks in product(range(4), repeat=2):
            state = initial_state(2)
            weight = 0
            for mask in masks:
                outgoing = advance_row(state, mask)
                if outgoing is None:
                    break
                deltas = tile_grammar_row_deltas(state, mask, outgoing)
                weight += 3 * deltas.u_count - 2 * deltas.rank_delta - 1
                state = outgoing
            else:
                weights.append(weight)
        corridor = build_equality_corridor(2)
        self.assertEqual(corridor.minimum_weight, min(weights))
        self.assertEqual(corridor.minimum_path_count, weights.count(min(weights)))

    def test_every_n3_corridor_edge_satisfies_the_global_equality(self) -> None:
        corridor = build_equality_corridor(3)
        retained = [set(edges) for edges in corridor.corridor_edges]
        for row in range(3):
            incident_in = set()
            incident_out = set()
            for incoming_key, incoming in corridor.layers[row].items():
                for mask in range(1 << 3):
                    outgoing = advance_row(incoming, mask)
                    if outgoing is None:
                        continue
                    edge = _edge(row, incoming_key, incoming, mask, outgoing)
                    remaining = corridor.backward[row + 1].get(edge.outgoing)
                    is_optimal = remaining is not None and (
                        corridor.forward[row][incoming_key] + edge.weight + remaining
                        == corridor.minimum_weight
                    )
                    self.assertEqual(edge in retained[row], is_optimal)
                    if is_optimal:
                        incident_in.add(edge.incoming)
                        incident_out.add(edge.outgoing)
            self.assertEqual(incident_in, corridor.corridor_states[row])
            self.assertEqual(incident_out, corridor.corridor_states[row + 1])

    def test_structural_quotient_ignores_cumulative_fields(self) -> None:
        start = initial_state(4)
        first = advance_row(start, 0b0110)
        self.assertIsNotNone(first)
        shifted = replace(first, u_cost=first.u_cost + 17, cycle_excess=first.cycle_excess + 9)
        ordinary = advance_row(first, 0b1110)
        shifted_out = advance_row(shifted, 0b1110)
        self.assertIsNotNone(ordinary)
        self.assertIsNotNone(shifted_out)
        self.assertEqual(structural_key(ordinary), structural_key(shifted_out))
        self.assertEqual(
            tile_grammar_row_deltas(first, 0b1110, ordinary),
            tile_grammar_row_deltas(shifted, 0b1110, shifted_out),
        )

    def test_cached_residue_two_comparison_records_profile_break(self) -> None:
        artifact = json.loads(
            Path(__file__).with_name("residue_two_equality_comparison.json").read_text()
        )
        self.assertEqual(artifact["corridors"]["8"]["minimum_weight"], 5)
        self.assertEqual(artifact["corridors"]["8"]["minimum_path_count"], "704")
        self.assertEqual(
            artifact["corridors"]["8"]["corridor_states_by_row"],
            [1, 20, 20, 22, 37, 24, 38, 26, 20],
        )
        self.assertEqual(
            artifact["corridors"]["8"]["corridor_transitions_by_row"],
            [20, 20, 67, 47, 40, 48, 92, 34],
        )
        self.assertEqual(
            artifact["normalized_overlap"],
            {
                "packet": {"state_profiles": 4, "transition_profiles": 11},
                "overlap": {"state_profiles": 4, "transition_profiles": 19},
                "local": {"state_profiles": 4, "transition_profiles": 0},
                "transport": {"state_profiles": 4, "transition_profiles": 0},
                "attachment": {"state_profiles": 0, "transition_profiles": 0},
                "full": {"state_profiles": 0, "transition_profiles": 0},
            },
        )
        self.assertEqual(artifact["traces"]["14"]["packet"]["matched_baseline_rows"], [12])
        self.assertEqual(artifact["traces"]["17"]["packet"]["matched_baseline_rows"], [])

    @unittest.skipUnless(os.environ.get("GRID_GRAPHS_SLOW"), "slow exact regeneration")
    def test_cached_residue_two_comparison_regenerates_exactly(self) -> None:
        artifact = json.loads(
            Path(__file__).with_name("residue_two_equality_comparison.json").read_text()
        )
        self.assertEqual(residue_two_comparison(), artifact)

    @unittest.skipUnless(os.environ.get("GRID_GRAPHS_SLOW"), "slow n=7 corridor")
    def test_n7_corridor_census(self) -> None:
        corridor = build_equality_corridor(7)
        self.assertEqual((corridor.minimum_weight, corridor.minimum_u), (2, 27))
        self.assertEqual(corridor.minimum_path_count, 16)
        self.assertEqual(
            [len(layer) for layer in corridor.corridor_states],
            [1, 5, 5, 4, 4, 4, 5, 5],
        )


if __name__ == "__main__":
    unittest.main()
