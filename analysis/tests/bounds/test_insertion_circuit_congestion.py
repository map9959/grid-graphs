from __future__ import annotations

import unittest

from analysis.bounds.insertion_circuit_congestion import (
    canonical_insertion_circuits,
    congestion_profile,
    insertion_circuit_options,
    select_insertion_circuits,
    turning_inequality_margin,
)


class InsertionCircuitCongestionTests(unittest.TestCase):
    def test_two_by_two_chooses_the_unique_cell_boundary(self) -> None:
        circuits = canonical_insertion_circuits(2, (0b11, 0b00))
        self.assertEqual(len(circuits), 2)
        for circuit in circuits:
            self.assertEqual(circuit.length, 4)
            self.assertEqual(circuit.turns, 4)
            self.assertEqual(circuit.enclosed_cells, (0,))
            self.assertEqual(len(circuit.inserted_edges), 1)

        profile = congestion_profile(2, (0b11, 0b00))
        self.assertEqual(profile["resources"]["cells"]["maximum_load"], 2)
        self.assertEqual(profile["resources"]["U_U_edges"]["maximum_load"], 2)
        self.assertEqual(profile["strengthened_margin"], 0)

    def test_canonical_result_is_deterministic_and_simple(self) -> None:
        rows = (0b1001, 0b1001, 0b0000, 0b1111)
        first = canonical_insertion_circuits(4, rows)
        second = canonical_insertion_circuits(4, rows)
        self.assertEqual(first, second)
        for circuit in first:
            self.assertEqual(len(circuit.edges), len(set(circuit.edges)))
            self.assertEqual(circuit.vertices[0], circuit.vertices[-1])
            self.assertEqual(len(circuit.vertices) - 1, len(circuit.edges))

    def test_noncanonical_quantifiers_have_a_three_by_three_counterexample(self) -> None:
        rows = (0b001, 0b100, 0b101)
        profile = congestion_profile(3, rows)
        self.assertEqual(
            profile["turning_margins_by_quantifier"],
            {
                "shortest_lex": 2,
                "minimum_turns": 2,
                "maximum_turns": -2,
                "all_circuits": -30,
            },
        )
        options = insertion_circuit_options(3, rows)
        canonical = canonical_insertion_circuits(3, rows)
        self.assertTrue(any(len(owner_options) > 1 for owner_options in options))
        self.assertTrue(
            all(circuit in owner_options for circuit, owner_options in zip(canonical, options))
        )

    def test_shortest_lex_is_not_a_minimum_turn_definition(self) -> None:
        rows = tuple(
            int(row[::-1].replace("F", "1").replace("U", "0"), 2)
            for row in (
                "FUFFFFFFUUFFF",
                "FUUUUUUUUUUUU",
                "FUUFUUFUFFUFU",
                "FUUFUUUUUUUUU",
                "FUUUUFFUUFFUF",
                "UUFFUUUUUUUUF",
                "FUUUUUFUUUUUU",
                "FUUUFUUUFUFFF",
                "UUUUFUUUUUUUU",
                "FFFUFUUUFFUUF",
                "UUUUUUFUUUUUF",
                "FUUUUUFUUUFUF",
                "FUFFFUFUFUUUF",
            )
        )
        self.assertEqual(turning_inequality_margin(13, rows, "shortest_lex"), 25)
        self.assertEqual(turning_inequality_margin(13, rows, "minimum_turns"), 27)
        self.assertNotEqual(
            select_insertion_circuits(13, rows, "shortest_lex"),
            select_insertion_circuits(13, rows, "minimum_turns"),
        )

    def test_turning_inequality_on_every_maximal_set_through_five(self) -> None:
        from analysis.bounds.bundle_cycle_defect_census import maximal_profiles

        expected = {
            2: (4, 0, 4),
            3: (26, 2, 0),
            4: (138, 0, 14),
            5: (2164, 3, 0),
        }
        counts = []
        for n in range(2, 6):
            count = 0
            margins = []
            for rows, profile in maximal_profiles(n):
                circuits = canonical_insertion_circuits(n, rows)
                self.assertEqual(len(circuits), profile.unforced)
                turn_excess = sum(circuit.turns - 4 for circuit in circuits)
                margins.append(profile.component_strengthened_margin - turn_excess)
                count += 1
            counts.append(count)
            self.assertEqual(
                (count, min(margins), margins.count(0)), expected[n]
            )
        self.assertEqual(counts, [4, 26, 138, 2164])

    def test_turning_inequality_on_larger_canonical_witnesses(self) -> None:
        from analysis.bounds.boundary_charge_reduction import canonical_rows
        from analysis.bounds.bundle_cycle_defect_census import defect_profile

        for n in range(6, 16):
            rows = canonical_rows(n)
            profile = defect_profile(n, rows)
            circuits = canonical_insertion_circuits(n, rows)
            turn_excess = sum(circuit.turns - 4 for circuit in circuits)
            self.assertGreaterEqual(
                profile.component_strengthened_margin - turn_excess, 0
            )


if __name__ == "__main__":
    unittest.main()
