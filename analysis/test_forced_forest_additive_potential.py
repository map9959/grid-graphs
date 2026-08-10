from __future__ import annotations

import json
import unittest
from fractions import Fraction
from pathlib import Path


ARTIFACT = Path(__file__).with_name("forced_forest_additive_potential.json")


class ForcedForestAdditivePotentialTests(unittest.TestCase):
    def test_exact_conflicts_replay(self) -> None:
        artifact = json.loads(ARTIFACT.read_text())
        for name, experiment in artifact["experiments"].items():
            with self.subTest(name=name):
                compression = experiment["symbolic_compression"]
                self.assertFalse(compression["fits"])
                conflict = compression["exact_conflict"]
                equations = conflict["equations"]
                categories = {tuple(item["feature"][:3]) for item in equations}
                self.assertEqual(len(categories), 1)
                multipliers = [Fraction(*item["multiplier"]) for item in equations]
                self.assertEqual(sum(multipliers), 0)
                numeric_columns = zip(*(item["feature"][3:] for item in equations))
                self.assertTrue(
                    all(
                        sum(
                            multiplier * value
                            for multiplier, value in zip(multipliers, column)
                        )
                        == 0
                        for column in numeric_columns
                    )
                )
                rhs = sum(
                    multiplier * Fraction(*item["lookup_potential"])
                    for multiplier, item in zip(multipliers, equations)
                )
                self.assertEqual(rhs, Fraction(*conflict["nonzero_right_hand_side"]))
                self.assertNotEqual(rhs, 0)


if __name__ == "__main__":
    unittest.main()
