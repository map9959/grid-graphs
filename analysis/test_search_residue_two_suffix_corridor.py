from __future__ import annotations

import json
import unittest
from collections import Counter
from itertools import product

from construction_lab import dual_connectivity_check, forest_completion_check
from search_residue_two_middle import BASIC_ALPHABET, KNOWN_250
from search_residue_two_suffix_corridor import (
    DEFAULT_CERTIFICATE,
    FIRST_MUTABLE_ROW,
    LAST_MUTABLE_ROW,
    MUTABLE_PACKET_COLUMNS,
    N,
    certificate,
    exact_state_key,
    packet_domains,
    search,
    validate_scope,
)
from tile_grammar import FrontierState, advance_row, initial_state, row_mask, stream_row_packets


def state_before_row(row: int) -> FrontierState:
    state = initial_state(N)
    for value in KNOWN_250[:row]:
        child = advance_row(state, row_mask(value))
        if child is None:
            raise AssertionError("KNOWN_250 prefix sealed unexpectedly")
        state = child
    return state


class SuffixCorridorTests(unittest.TestCase):
    def test_declared_scope_is_exactly_fourteen_packets(self) -> None:
        validate_scope()
        mutable = []
        for row in range(FIRST_MUTABLE_ROW, LAST_MUTABLE_ROW + 1):
            domains = packet_domains(row)
            mutable.extend((row, column) for column, domain in enumerate(domains) if len(domain) > 1)
            self.assertTrue(all(len(domains[column]) == 1 for column in range(2, 6)))
        self.assertEqual(
            mutable,
            [(row, column) for row in range(11, 18) for column in MUTABLE_PACKET_COLUMNS],
        )

    def test_exact_key_retains_unprojected_partition(self) -> None:
        left = FrontierState(N, 12, 7, (0, 1, 1), 100, 0)
        right = FrontierState(N, 12, 7, (0, 1, 2), 100, 0)
        self.assertNotEqual(exact_state_key(left), exact_state_key(right))

    def test_stream_matches_direct_advance_on_representative_corridor_rows(self) -> None:
        for row in (11, 14, 17):
            incoming = state_before_row(row)
            domains = packet_domains(row)
            streamed, _ = stream_row_packets(
                incoming,
                ".",
                ".",
                domains,
                packet_alphabet=BASIC_ALPHABET,
            )
            stream_multiset = Counter(
                (transition.outgoing, transition.row_mask, transition.packet_names)
                for transition in streamed
            )
            direct_multiset = Counter()
            for names in product(*domains):
                value = "." + "".join(BASIC_ALPHABET[name] for name in names) + "."
                mask = row_mask(value)
                outgoing = advance_row(incoming, mask)
                if outgoing is not None:
                    direct_multiset[(outgoing, mask, names)] += 1
            self.assertEqual(stream_multiset, direct_multiset)
            self.assertEqual(sum(stream_multiset.values()), sum(direct_multiset.values()))

    def test_singleton_known_path_reconstructs_known_250(self) -> None:
        result = search(target_u=250, variable=False, report=False)
        self.assertEqual(result.witness, KNOWN_250)
        self.assertEqual(result.accepted_assignments, 1)
        self.assertTrue(dual_connectivity_check(result.witness)[0])
        self.assertTrue(forest_completion_check(result.witness)[0])

    def test_exact_corridor_is_negative_with_stable_counts(self) -> None:
        result = search(report=False)
        self.assertIsNone(result.witness)
        self.assertEqual(result.final_states, 0)
        self.assertEqual(
            [row.outgoing_states for row in result.stats],
            [2, 11, 37, 90, 97, 46, 2, 2, 0],
        )
        self.assertEqual(
            [row.assignments_represented for row in result.stats],
            [2, 11, 40, 136, 247, 127, 3, 3, 0],
        )

    def test_committed_certificate_matches_fresh_exact_result(self) -> None:
        result = search(report=False)
        committed = json.loads(DEFAULT_CERTIFICATE.read_text())
        self.assertEqual(committed, certificate(result))


if __name__ == "__main__":
    unittest.main()
