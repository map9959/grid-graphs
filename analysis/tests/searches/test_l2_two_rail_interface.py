"""Finite witness checks and a one-node budget test; no full optimization."""

import unittest

from analysis.searches import l2_two_rail_interface as interface
from analysis.searches import l2_rail_repair_research as repair


class TwoRailInterfaceTests(unittest.TestCase):
    def test_window_and_bounds(self):
        for s, count in ((2, 30), (3, 36)):
            n, source, fixed, variable = interface.endpoint_window(s)
            h = 3 * s
            self.assertEqual(len(variable), count)
            self.assertEqual(fixed, source - variable)
            self.assertTrue(variable.isdisjoint(fixed))
            self.assertTrue({(h - 3, h + 2), (h, h + 2),
                             (h - 3, h + 4), (h, h + 4)} <= variable)
            repair.forced_partition(n, fixed)
        for s in (-1, 0, 1, 4, 5, 100):
            with self.assertRaises(ValueError):
                interface.endpoint_window(s)
            with self.assertRaises(ValueError):
                interface.double_cut(s)

    def test_two_rootless_rails_and_isolates(self):
        for s, sizes in ((2, [1, 11, 82, 1, 1]), (3, [1, 17, 141, 1, 1])):
            n, fixed = interface.double_cut(s)
            h = 3 * s
            ports = [(h - 3, h + 1), (h, h + 1), (h + 3, h + 1)]
            self.assertEqual(len(interface.attachment_partition(n, fixed, ports)), 3)
            bridge = (h + 2, h + 1)
            attachments = [bridge] + repair.neighbors(n, bridge)
            blocks = interface.attachment_partition(n, fixed, attachments)
            self.assertEqual(len(blocks), 5)
            result, signatures = repair.audit_insertions(n, fixed, [{bridge}])
            self.assertEqual(signatures, [(bridge, sizes)])
            self.assertEqual(interface.attachment_partition(n, result, ports),
                             ((ports[0],), (ports[1], ports[2])))
            parent = repair.forced_partition(n, result)
            self.assertIsNone(repair.insert(n, result, parent, (h + 2, s + 3)))
            _, source = repair.staircase(s)
            pocket = {v for v in source if v[0] in (h + 1, h + 2) and
                      2 <= v[1] <= h + 2}
            restored, _ = repair.audit_insertions(n, result, [{v} for v in sorted(pocket)])
            self.assertEqual(len(restored), len(source) - 1)
            self.assertEqual(interface.attachment_partition(n, restored, ports),
                             ((ports[0],), (ports[1], ports[2])))

    def test_intact_rail_square_despite_distinct_roots(self):
        for s in (2, 3):
            n, fixed = interface.double_cut(s)
            h = 3 * s
            for c in range(s + 4, h + 1):
                u = (h - 1, c)
                parent = repair.forced_partition(n, fixed)
                self.assertNotEqual(repair.root(parent, u),
                                    repair.root(parent, (h - 2, c)))
                self.assertEqual(repair.root(parent, u),
                                 repair.root(parent, (h - 1, c - 1)))
                self.assertIsNone(repair.insert(n, fixed, parent, u))
                square = [u, (h, c), (h, c - 1), (h - 1, c - 1)]
                for a, b in zip(square, square[1:]):
                    self.assertIn(b, repair.neighbors(n, a))
                    self.assertTrue(a in fixed or b in fixed)
                self.assertNotIn(u, fixed)
                self.assertNotIn(square[-1], fixed)

    def test_reported_maximizers_replay(self):
        for s in (2, 3):
            n, source, fixed, variable = interface.endpoint_window(s)
            result = source - {(8, 4)} | {(7, 3)} if s == 2 else source
            self.assertTrue(fixed <= result <= fixed | variable)
            self.assertEqual(repair.profile(n, result),
                             {"f": 48 if s == 2 else 76,
                              "r": 9 if s == 2 else 12, "c": 7, "b": 5})

    def test_joined_rootless_witness_and_paid_extension(self):
        for s in (2, 3):
            n, source, fixed, variable = interface.notch_window(s)
            h = 3 * s
            self.assertEqual(len(variable), 34 if s == 2 else 40)
            _, witness = interface.joined_witness(s)
            self.assertTrue(fixed <= witness <= fixed | variable)
            replay, _ = repair.audit_insertions(
                n, source & witness, [{v} for v in sorted(witness - source)])
            self.assertEqual(replay, witness)
            a, u, e = (h - 3, s + 2), (h - 1, s + 4), (h + 1, s + 4)
            d, m = (h, h + 1), (h + 3, h + 1)
            self.assertEqual(interface.attachment_partition(n, witness, [a, u, e, d, m]),
                             (tuple(sorted((a, u, e))), tuple(sorted((d, m)))))
            self.assertEqual(repair.profile(n, witness),
                             {"f": 47 if s == 2 else 75,
                              "r": 11 if s == 2 else 14, "c": 7, "b": 6})
            boundary = [v for v in repair.forced_partition(n, witness)
                        if v[0] in (0, n - 1) or v[1] in (0, n - 1)]
            parent = repair.forced_partition(n, witness)
            root = repair.root(parent, a)
            self.assertTrue(all(repair.root(parent, b) != root for b in boundary))
            self.assertEqual(sum(repair.root(parent, v) == root for v in parent),
                             31 if s == 2 else 37)
            next_center = (h + 1, s + 5)
            self.assertIsNone(repair.insert(n, witness, parent, next_center))
            self.assertEqual(repair.root(parent, (h, s + 5)),
                             repair.root(parent, (h + 1, s + 6)))
            extended, signatures = repair.audit_insertions(
                n, witness - {(h, s + 6)}, [{next_center}])
            self.assertEqual(signatures, [(next_center, [31 if s == 2 else 37, 1, 1, 1])])
            self.assertEqual(len(extended), len(witness))
            parent = repair.forced_partition(n, extended)
            self.assertTrue(all(repair.root(parent, b) != repair.root(parent, a)
                                for b in boundary))
            following = (h + 1, s + 6)
            updated = repair.insert(n, extended, parent, following)
            if s == 2:
                self.assertIsNotNone(updated)
                self.assertEqual(repair.root(updated, a), repair.root(updated, m))
                repair.audit_insertions(n, extended, [{following}])
            else:
                self.assertIsNone(updated)
                self.assertEqual(repair.root(parent, (h, s + 6)),
                                 repair.root(parent, (h + 1, s + 7)))

    def test_budget_limited_status_and_guards(self):
        result = interface.search_notch(2, "joined-rootless", node_budget=1)
        self.assertEqual(result["nodes"], 1)
        self.assertFalse(result["exhaustive"])
        repair.forced_partition(11, result["centers"])
        with self.assertRaises(ValueError):
            interface.search_notch(2, "joined-rootless", node_budget=0)
        with self.assertRaises(ValueError):
            interface.search_notch(2, "unknown")
        for s in (1, 4, 100):
            with self.assertRaises(ValueError):
                interface.notch_window(s)
            with self.assertRaises(ValueError):
                interface.joined_witness(s)
            with self.assertRaises(ValueError):
                interface.search_notch(s, "rootless")


if __name__ == "__main__":
    unittest.main()
