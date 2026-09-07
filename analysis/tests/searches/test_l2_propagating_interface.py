"""Fixed two-seed interface replays; no exhaustive search on import or in tests."""

import unittest

from analysis.searches import l2_propagating_interface as interface
from analysis.searches import l2_rail_repair_research as repair


class PropagatingInterfaceTests(unittest.TestCase):
    def test_continuation_merges_then_blocks(self):
        for s, expected in ((2, [92, 18, 1, 1]), (3, [158, 24, 1, 1])):
            with self.subTest(s=s):
                n, fixed, pieces, blocked = interface.continuation(s)
                centers, signatures = repair.audit_insertions(n, fixed, pieces)
                self.assertEqual(signatures[0][1], expected)
                parent = repair.forced_partition(n, centers)
                self.assertIsNone(repair.insert(n, centers, parent, blocked))
                collision = (3 * s + 1, 3 * s + 3) if s == 2 else (3 * s, s + 6)
                self.assertEqual(repair.root(parent, blocked), repair.root(parent, collision))
                self.assertEqual(len(centers), 48 if s == 2 else 75)

    def test_sweep_supports_and_actual_components(self):
        for s, expected in ((2, {"f": 48, "r": 9, "c": 7, "b": 5}),
                            (3, {"f": 75, "r": 11, "c": 11, "b": 5})):
            with self.subTest(s=s):
                n, fixed, pieces = interface.swept_interface(s)
                h = 3 * s
                parent = repair.forced_partition(n, fixed)
                labels = {repair.root(parent, v) for v in fixed}
                self.assertEqual(len(labels), 2)
                main = repair.root(parent, (0, 0))
                detached = repair.root(parent, (h - 3, s + 2))
                self.assertNotEqual(main, detached)
                self.assertEqual(sum(repair.root(parent, v) == detached for v in parent),
                                 6 * s + 2)
                old_support = fixed | {w for v in fixed for w in repair.neighbors(n, v)}
                supports = [piece | {w for v in piece for w in repair.neighbors(n, v)}
                            for piece in pieces]
                self.assertEqual(supports[0] & old_support, {(h - 2, s + 4)})
                self.assertEqual(supports[1] & old_support, {(h, s + 1)})
                self.assertEqual(supports[0] & supports[1], {(h, s + 4)})
                self.assertEqual(repair.root(parent, (h - 2, s + 4)), detached)
                self.assertEqual(repair.root(parent, (h, s + 1)), main)
                centers, _ = repair.audit_insertions(n, fixed, pieces)
                self.assertEqual(repair.profile(n, centers), expected)
                final = repair.forced_partition(n, centers)
                self.assertEqual(len({repair.root(final, v) for v in centers}), 1)

    def test_size_guards(self):
        for constructor in (interface.preceding_cut, interface.continuation,
                            interface.swept_interface):
            for s in (1, 4):
                with self.subTest(constructor=constructor.__name__, s=s):
                    with self.assertRaises(ValueError):
                        constructor(s)


if __name__ == "__main__":
    unittest.main()
