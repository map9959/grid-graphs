import json
import unittest
from analysis._paths import analysis_path
from analysis.tests._support import migrated_artifact



class AnnulusStreamingResultTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.result = migrated_artifact(json.loads(
            analysis_path("annulus_streaming_n11_side5_result.json")
            .read_text()
        ))
        cls.shards = migrated_artifact(json.loads(
            analysis_path("annulus_side7_threshold_automaton_shards.json")
            .read_text()
        ))

    def test_result_declares_exact_finite_scope(self) -> None:
        scope = self.result["scope"]
        self.assertEqual((scope["global_side"], scope["u_count"]), (11, 72))
        self.assertEqual(scope["centered_side"], 5)
        self.assertTrue(scope["pruning"].startswith("none"))
        self.assertFalse(self.result["result"]["any_violation"])

    def test_exhaustive_control_and_resource_gate_are_explicit(self) -> None:
        control = self.result["operational_exactness"][
            "rust_stream_vs_rust_terminal"
        ]
        self.assertEqual(control["patterns_checked"], 1 << 25)
        self.assertEqual(control["result"], "agree")
        self.assertEqual(self.result["larger_sides"]["attempted"], [7])
        self.assertEqual(self.result["larger_sides"]["not_attempted"], [9, 11])
        self.assertLess(
            self.result["result"]["maximum_resident_set_kib"],
            self.result["larger_sides"]["memory_gate_kib"],
        )
        partial = self.result["larger_sides"]["side_7_partial"]
        self.assertLess(partial["peak_rss_kib"], 6 * 1024 * 1024)
        self.assertLess(
            partial["last_completed_local_position"], partial["local_cells_total"]
        )

    def test_artifact_contains_replay_commands(self) -> None:
        commands = self.result["commands"]
        self.assertIn("--side 5", commands["search"])
        self.assertIn("--ignored", commands["exhaustive_side5"])
        self.assertIn(
            "threshold_automaton_agrees", commands["exhaustive_threshold_automaton_side5"]
        )
        self.assertIn("cargo test", commands["rust_tests"])
        self.assertIn("--as=6442450944", commands["side_7_gated_telemetry"])

    def test_side7_manifest_requires_complete_exact_repartition(self) -> None:
        self.assertEqual(self.shards["partition"]["shards"], 256)
        self.assertIn("full record-key equality", self.shards["partition"]["equality"])
        self.assertFalse(self.shards["safety"]["beam"])
        self.assertFalse(self.shards["safety"]["hash_collision_merging"])
        self.assertFalse(self.shards["safety"]["missing_shards_allowed"])
        self.assertIn("bitwise OR", self.shards["aggregate_criterion"])


if __name__ == "__main__":
    unittest.main()
