import unittest

from straight_carrier_count import check_carriers, exhaustive_sets


class StraightCarrierCountTest(unittest.TestCase):
    def test_branch_congestion_counterexample(self) -> None:
        # Two singleton carriers share the central branching U vertex.
        result = check_carriers(3, (0, 0b101, 0))
        self.assertEqual(result.branching_excess, 1)
        self.assertEqual(result.branching_u, 1)
        self.assertEqual(result.naive_summation_margin, -1)
        self.assertEqual(
            sum(c.quotient_degree - c.pendant_u_neighbors for c in result.carriers),
            2,
        )

    def test_every_forced_forest_through_three(self) -> None:
        for n in range(2, 4):
            for rows in exhaustive_sets(n):
                result = check_carriers(n, rows)
                self.assertGreaterEqual(result.target_margin, 0)


if __name__ == "__main__":
    unittest.main()
