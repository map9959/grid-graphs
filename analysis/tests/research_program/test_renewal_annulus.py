"""Lightweight geometry, exact encoding, and independent-audit tests; no search."""

import itertools
import unittest

from analysis.research_program.renewal_annulus import (
    CNF, audit, build_model, geometry, verify_witness,
)


class RenewalAnnulusTests(unittest.TestCase):
    def test_exact_frozen_coordinates(self):
        core8, free8 = geometry(8)
        self.assertEqual(core8, [3*8+4])
        self.assertEqual(len(free8), 60)
        expected = {(3, 4), (5, 5), (8, 8)}
        expected |= {(r, 7) for r in range(3, 7)}
        expected |= {(r, 10) for r in range(3, 10)}
        expected |= {(r, 3) for r in range(5, 11)}
        expected |= {(r, 6) for r in range(8, 11)}
        core14, free14 = geometry(14)
        self.assertEqual(set(map(lambda v: divmod(v, 14), core14)), expected)
        self.assertEqual(len(core14), 23)
        self.assertEqual(len(free14), 132)
        for n, core in ((8, core8), (14, core14)):
            self.assertTrue(audit(n, core)["forest"])

    def test_size_and_round_guards(self):
        for n in (0, 11, 15, 17):
            with self.assertRaises(ValueError):
                geometry(n)
        for rounds in (0, 10001):
            with self.assertRaises(ValueError):
                build_model(8, rounds)

    def test_threshold_recurrence_truth_table(self):
        # Exhaust every auxiliary assignment on tiny formulas, independently
        # checking existential equivalence, including impossible thresholds.
        for target in range(4):
            cnf = CNF()
            xs = [cnf.new(), cnf.new()]
            cnf.at_least(xs, target)
            for bits in itertools.product((False, True), repeat=2):
                possible = False
                for aux in itertools.product((False, True), repeat=cnf.variables-2):
                    assignment = (False,) + bits + aux
                    if all(any(assignment[abs(x)] == (x > 0) for x in clause)
                           for clause in cnf.clauses):
                        possible = True
                        break
                self.assertEqual(possible, sum(bits) >= target)

    def test_full_graph_and_ledger(self):
        empty = audit(8, [])
        self.assertEqual((empty["c"], empty["z"], empty["b"]), (64, 64, 32))
        star = audit(8, [3*8+4])
        self.assertEqual((star["f"], star["r"], star["c"], star["z"]), (1, 1, 60, 59))
        # Opposite centers force a unit square although the FF graph is edgeless.
        cyclic = audit(8, [3*8+3, 4*8+4])
        self.assertFalse(cyclic["forest"])
        self.assertEqual(cyclic["cycle_rank"], 1)
        self.assertEqual(cyclic["ff_cycle_rank"], 0)
        with self.assertRaises(ValueError):
            verify_witness(8, [3*8+4], 26)
        with self.assertRaises(ValueError):
            verify_witness(8, [3*8+3], 1)


if __name__ == "__main__":
    unittest.main()
