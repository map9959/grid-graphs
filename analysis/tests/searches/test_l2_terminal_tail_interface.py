"""Finite graph replays; optimization is limited to one-node status checks."""

import unittest

from analysis.searches import l2_terminal_tail_interface as tail
from analysis.searches import l2_rail_repair_research as repair


class TerminalTailTests(unittest.TestCase):
    def test_domains_and_guards(self):
        for s in (2, 3):
            h = 3 * s
            for left in (False, True):
                n, source, fixed, variable = tail.window(s, left)
                self.assertEqual(len(variable), {(2, False): 34, (2, True): 39,
                                                 (3, False): 42, (3, True): 48}[s, left])
                self.assertEqual(fixed, source - variable)
                self.assertTrue({(h, c) for c in range(s + 3, h + 3)} <= variable)
                self.assertTrue({(h + 1, c) for c in range(h + 2, h + 5)} <= variable)
                if left:
                    self.assertTrue({(h - 1, c) for c in range(s + 2)} <= variable)
        for s in (1, 4, 100):
            with self.assertRaises(ValueError):
                tail.window(s)
            with self.assertRaises(ValueError):
                tail.witness(s)
        with self.assertRaises(ValueError):
            tail.search(2, node_budget=0)
        with self.assertRaises(ValueError):
            tail.search(2, reach="unknown")
        with self.assertRaises(ValueError):
            tail.search(2, reach="left")

    def test_witnesses_full_components_and_attachment(self):
        expected = {(2, False): (47, 11, 6, 7, 37, 80),
                    (2, True): (47, 11, 6, 7, 40, 77),
                    (3, False): (76, 13, 6, 5, 43, 149),
                    (3, True): (75, 12, 10, 5, 46, 142)}
        for (s, left), (f, r, c, b, output_size, frame_size) in expected.items():
            n, source, fixed, variable = tail.window(s, left)
            _, centers = tail.witness(s, left)
            self.assertTrue(fixed <= centers <= fixed | variable)
            replay, _ = repair.audit_insertions(
                n, centers & source, [{v} for v in sorted(centers - source)])
            self.assertEqual(replay, centers)
            self.assertEqual(repair.profile(n, centers), dict(f=f, r=r, c=c, b=b))
            blocks = tail.components(n, centers)
            self.assertEqual(len(blocks), c)
            self.assertEqual(sum(map(len, blocks)), n * n)
            self.assertEqual(len(set().union(*map(set, blocks))), n * n)
            self.assertEqual(sorted(map(len, blocks)), [1] * (c - 2) + [output_size, frame_size])
            h = 3 * s
            output = next(block for block in blocks if (h - 3, s + 2) in block)
            self.assertEqual(len(output), output_size)
            self.assertTrue(tail.required_centers(s, "both" if left else "right") <= set(output))
            self.assertTrue(all(0 < r < n - 1 and 0 < c < n - 1 for r, c in output))
            self.assertNotIn((h + 3, h + 1), output)

    def test_cap_attachment_and_left_cost(self):
        n, centers = tail.witness(3)
        cap = (8, 11)
        before = centers - {cap}
        parent = repair.forced_partition(n, before)
        ports = [cap] + [v for v in repair.neighbors(n, cap) if v not in before]
        self.assertEqual(len({repair.root(parent, v) for v in ports}), len(ports))
        output = repair.root(parent, (6, 5))
        self.assertTrue(all(repair.root(parent, v) != output for v in ports))
        replay, _ = repair.audit_insertions(n, before, [{cap}])
        self.assertEqual(replay, centers)
        # Extending left hits repeated actual frame ports, closing a cycle.
        update = repair.insert(n, centers, repair.forced_partition(n, centers), (10, 4))
        self.assertIsNone(update)
        # Deleting that last rail center alone is insufficient: the pocket also touches.
        cut = centers - {(8, 4)}
        update = repair.insert(n, cut, repair.forced_partition(n, cut), (10, 4))
        self.assertIsNone(update)
        cut -= {(11, 3)}
        replay, _ = repair.audit_insertions(n, cut, [{(10, 4)}])
        self.assertEqual(replay, tail.witness(3, left=True)[1])

    def test_budget_is_lower_bound(self):
        for s in (2, 3):
            result = tail.search(s, node_budget=1)
            self.assertEqual(result["nodes"], 1)
            self.assertFalse(result["exhaustive"])
            self.assertEqual(result["components"], tail.components(3 * s + 5, result["centers"]))


if __name__ == "__main__":
    unittest.main()
