"""Replay only the fixed 11x11 and 14x14 repairs; never run a search."""

import unittest

from analysis.searches import l2_rail_repair_research as repair


class L2RailRepairTests(unittest.TestCase):
    def test_fixed_seed_repairs(self):
        cases = (
            (2, {"f": 49, "r": 11, "c": 2, "b": 5}, [
                ((5, 6), [1, 102, 1, 1, 1]),
                ((7, 3), [1, 106, 1, 1, 1]),
                ((7, 4), [110, 1, 1, 1]),
                ((7, 5), [113, 1, 1, 1]),
                ((8, 7), [1, 1, 116, 1, 1]),
            ]),
            (3, {"f": 76, "r": 13, "c": 6, "b": 5}, [
                ((8, 7), [1, 173, 1, 1, 1]),
                ((10, 4), [1, 177, 1, 1, 1]),
                ((10, 5), [181, 1, 1, 1]),
                ((10, 6), [184, 1, 1, 1]),
                ((11, 8), [1, 1, 187, 1, 1]),
            ]),
        )
        for s, expected_profile, expected_insertions in cases:
            with self.subTest(s=s):
                n, fixed, pieces = repair.repaired_staircase(s)
                repair.check_support_invariant(n, s, fixed, pieces)
                centers, signatures = repair.audit_insertions(n, fixed, pieces)
                self.assertEqual(signatures, expected_insertions)
                self.assertEqual(centers - fixed, {v for v, _ in expected_insertions})
                self.assertEqual(repair.profile(n, centers), expected_profile)
                _, original = repair.staircase(s)
                self.assertEqual(len(original), 48 if s == 2 else 76)
                self.assertEqual(len(centers) - len(original), 1 if s == 2 else 0)

                # Check component identities, not just the printed size signature.
                parent = repair.forced_partition(n, fixed)
                for v, _ in expected_insertions:
                    attachments = [v] + [w for w in repair.neighbors(n, v) if w not in fixed]
                    self.assertEqual(len({repair.root(parent, w) for w in attachments}),
                                     len(attachments))
                    updated = repair.insert(n, fixed, parent, v)
                    self.assertIsNotNone(updated)
                    parent = updated
                    fixed.add(v)

    def test_rootless_bridge_partition(self):
        for s, sizes in ((2, [1, 11, 98, 1, 1]), (3, [1, 17, 163, 1, 1])):
            with self.subTest(s=s):
                n, original = repair.staircase(s)
                h = 3 * s
                pocket = {(r, c) for r in (h + 1, h + 2) for c in range(2, h + 3)}
                fixed = original - pocket - {(h, h + 2)}
                parent = repair.forced_partition(n, fixed)
                v = (h + 2, h + 1)
                attachments = [v] + repair.neighbors(n, v)
                self.assertTrue(all(w not in fixed for w in attachments))
                self.assertEqual(len({repair.root(parent, w) for w in attachments}), 5)
                self.assertNotEqual(repair.root(parent, (h + 1, h + 1)),
                                    repair.root(parent, (h + 3, h + 1)))
                centers, signatures = repair.audit_insertions(n, fixed, [{v}])
                self.assertEqual(signatures, [(v, sizes)])
                before = repair.profile(n, fixed)
                after = repair.profile(n, centers)
                self.assertEqual(after["f"], before["f"] + 1)
                self.assertEqual(after["c"], before["c"] - 4)
                parent = repair.forced_partition(n, centers)
                self.assertIsNone(repair.insert(n, centers, parent, (h + 2, s + 3)))

    def test_seed_constructors_reject_out_of_scope_sizes(self):
        for constructor in (repair.staircase, repair.repaired_staircase):
            for s in (1, 4):
                with self.subTest(constructor=constructor.__name__, s=s):
                    with self.assertRaisesRegex(ValueError, "n <= 15"):
                        constructor(s)


if __name__ == "__main__":
    unittest.main()
