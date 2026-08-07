from __future__ import annotations

import json
import unittest

from residue_two_cut_potential_obstruction import DEFAULT_OUTPUT, build_artifact


class ResidueTwoCutPotentialObstructionTests(unittest.TestCase):
    def test_committed_obstruction_is_exact(self) -> None:
        artifact = json.loads(DEFAULT_OUTPUT.read_text())
        self.assertEqual(build_artifact(), artifact)
        self.assertEqual(
            [item["dominant_packet_increment"] for item in artifact["negative_self_loops"]],
            [-1, -1],
        )
        self.assertFalse(artifact["scope"]["weighted_word_potential_ruled_out"])
        self.assertEqual(artifact["proof"]["contradiction"], "-1>=0")


if __name__ == "__main__":
    unittest.main()
