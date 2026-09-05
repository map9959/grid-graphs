import unittest

from coupled_interval_potential import experiment


class CoupledIntervalPotentialTest(unittest.TestCase):
    def test_exact_gate_through_width_five(self) -> None:
        result = experiment([3, 4, 5])
        self.assertEqual(result["scope"]["terminal_target"], 4)
        self.assertTrue(result["result"]["feasible"])
        self.assertTrue(all(value >= 4 for value in result["result"]["terminal_minima"].values()))

    def test_extremal_interval_compression_through_width_five(self) -> None:
        result = experiment([3, 4, 5], "extrema")
        self.assertTrue(result["result"]["feasible"])


if __name__ == "__main__":
    unittest.main()
