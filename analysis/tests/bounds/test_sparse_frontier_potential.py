from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

from analysis.bounds import synthesize_sparse_frontier_potential as sparse


class SparsePotentialDiagnosticsTests(unittest.TestCase):
    def setUp(self) -> None:
        sparse.ACTIVE_BASIS = "hinges"
        sparse.ACTIVE_FEATURE_LEVEL = "runs"

    def test_lp_coefficients_are_not_artificially_bounded(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "candidate.lp"
            sparse.write_lp(path, ["x"], [({"x": 1}, "<=", 2)])
            model = path.read_text()
        self.assertNotIn("Bounds", model)
        self.assertNotIn("100", model)
        self.assertTrue(model.endswith("End\n"))

    def test_table_tree_is_large_and_fails_first_held_out_row(self) -> None:
        table = sparse.build_shortest_potential_table((3, 4, 5, 6))
        samples = [(sparse._tree_coordinates(feature), value) for feature, value in table]
        tree = sparse.build_decision_tree(samples)
        self.assertEqual(sparse._tree_stats(tree), (332, 15))
        self.assertEqual(
            sparse.validate_tree_width(tree, 7),
            {"n": 7, "valid": False, "row": 1, "mask": 0, "slack": [-6, 1]},
        )


if __name__ == "__main__":
    unittest.main()
