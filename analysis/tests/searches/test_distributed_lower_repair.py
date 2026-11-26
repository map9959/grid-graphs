"""Small deterministic replays; no optimization or large boards."""

import unittest

from analysis.searches.distributed_lower_repair import collision_motif, probe, seam
from analysis.searches.l2_rail_repair_research import profile


class DistributedLowerRepairTests(unittest.TestCase):
    def test_balanced_seeds(self):
        for s in (2, 3):
            for phases in ((2,) * s, tuple(range(2, s + 2))):
                n, centers = seam(s, phases)
                self.assertEqual(profile(n, centers)["f"], 3 * s * s + 12 * s + 11)

    def test_actual_collision_includes_center(self):
        _, blocks = collision_motif()
        self.assertEqual(blocks, [[(4, 4), (6, 4)], [(5, 3)], [(5, 4)], [(5, 5)]])

    def test_cutoff_and_guards(self):
        result = probe(3, node_cap=1)
        self.assertEqual(result["nodes"], 1)
        self.assertFalse(result["exhaustive"])
        self.assertEqual(result["layouts"], 0)
        with self.assertRaises(ValueError):
            seam(4, (2, 3, 4, 5))
        with self.assertRaises(ValueError):
            probe(2, node_cap=1001)
        with self.assertRaises(ValueError):
            seam(3, (2, 4, 2))


if __name__ == "__main__":
    unittest.main()
