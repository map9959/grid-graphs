from __future__ import annotations

import hashlib
import json
import unittest

from analysis._paths import ANALYSIS_ROOT
from analysis.tests._support import migrated_artifact

HERE = ANALYSIS_ROOT
ROOT = HERE.parent
MIRROR_RESULT = HERE / "frontier_n17_mirror_result.json"
UNMIRRORED_RESULT = HERE / "frontier_n17_unmirrored_result.json"


class FrontierN17ResultTests(unittest.TestCase):
    def test_unmirrored_result_confirms_exact_minimum(self) -> None:
        result = migrated_artifact(json.loads(UNMIRRORED_RESULT.read_text()))

        self.assertEqual(result["status"], "UNSAT")
        self.assertEqual((result["n"], result["u_count_limit"]), (17, 178))
        self.assertEqual((result["minimum_u"], result["p_n_n"]), (179, 110))
        self.assertEqual(result["pruning"], "none")
        self.assertEqual(result["state_set_empty_after_step"], 288)
        self.assertEqual(result["completed_steps"], 289)
        self.assertEqual(result["final_checkpoint"]["states"], 0)
        self.assertGreater(result["peak_states"], 85_000_000)
        self.assertGreater(result["generated_transitions"], 30_000_000_000)

    def test_source_and_cross_reference_match(self) -> None:
        result = migrated_artifact(json.loads(UNMIRRORED_RESULT.read_text()))
        mirror = migrated_artifact(json.loads(MIRROR_RESULT.read_text()))
        source = ROOT / "src/bin/search_n17_frontier.rs"

        self.assertEqual(hashlib.sha256(source.read_bytes()).hexdigest(), result["source_sha256"])
        verification = mirror["unmirrored_verification"]
        self.assertEqual(verification["status"], "COMPLETE_UNSAT")
        self.assertEqual(verification["result"], UNMIRRORED_RESULT.name)
        self.assertEqual(verification["peak_states"], result["peak_states"])
        self.assertEqual(
            verification["generated_transitions"], result["generated_transitions"]
        )
        self.assertEqual(
            verification["final_checkpoint_sha256"],
            result["final_checkpoint"]["sha256"],
        )


if __name__ == "__main__":
    unittest.main()
