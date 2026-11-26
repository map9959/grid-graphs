import unittest
from collections import defaultdict

from generate_square_tree import generate_square_tree, square_score


class GenerateSquareTreeTest(unittest.TestCase):
    def test_generated_trees(self):
        # Includes the small cases, all zipper phases, and a repeated comb cap.
        for n in (*range(1, 85), 161):
            with self.subTest(side=n):
                edges, full = generate_square_tree(n)
                self.assertEqual(len(edges), n * n - 1)
                adj = defaultdict(set)
                for (r, c), (i, j) in edges:
                    self.assertTrue(all(0 <= x < n for x in (r, c, i, j)))
                    self.assertEqual(abs(r - i) + abs(c - j), 1)
                    self.assertNotIn((i, j), adj[r, c])
                    adj[r, c].add((i, j))
                    adj[i, j].add((r, c))

                reached = {(0, 0)}
                stack = [(0, 0)]
                while stack:
                    unseen = adj[stack.pop()] - reached
                    reached.update(unseen)
                    stack.extend(unseen)
                self.assertEqual(len(reached), n * n)
                actual = {
                    (r, c) for r, c in reached
                    if len(adj[r, c]) == (r > 0) + (r < n - 1) + (c > 0) + (c < n - 1)
                }
                self.assertEqual(set(full), actual)
                self.assertEqual(len(actual), square_score(n))

    def test_known_scores(self):
        self.assertEqual([square_score(n) for n in range(1, 12)],
                         [1, 2, 4, 8, 11, 16, 22, 27, 34, 42, 49])
        self.assertEqual(square_score(161), 8791)

    def test_reject_nonpositive_side(self):
        with self.assertRaises(ValueError):
            generate_square_tree(0)
