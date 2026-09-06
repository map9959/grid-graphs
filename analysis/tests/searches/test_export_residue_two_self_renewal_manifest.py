from __future__ import annotations

import json
import unittest


from analysis.searches.export_residue_two_self_renewal_manifest import DEFAULT_OUTPUT, build_manifest
from analysis.tests._support import slow_test
from analysis._paths import analysis_path
from analysis.tests._support import migrated_artifact


class SelfRenewalManifestTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.manifest = migrated_artifact(json.loads(DEFAULT_OUTPUT.read_text()))

    @slow_test
    def test_committed_manifest_reproduces(self) -> None:
        self.assertEqual(self.manifest, build_manifest())

    def test_references_and_layers_are_consistent(self) -> None:
        states = {item["id"]: item for item in self.manifest["signature_states"]}
        domains = {item["id"]: item for item in self.manifest["mask_domains"]}
        self.assertTrue(self.manifest["top_seeds"])
        self.assertTrue(self.manifest["bottom_seeds"])
        for transition in self.manifest["signature_transitions"]:
            self.assertIn(transition["before"], states)
            self.assertIn(transition["after"], states)
            self.assertIn(transition["domain_id"], domains)
            self.assertEqual(states[transition["before"]]["layer"], transition["row"])
            self.assertEqual(states[transition["after"]]["layer"], transition["row"] + 1)
            self.assertEqual(
                states[transition["before"]]["lane"],
                states[transition["after"]]["lane"],
            )
        self.assertTrue(all(lane["active"] for lane in self.manifest["lanes"] if lane["top_seeds"] and lane["bottom_seeds"]))

    def test_discovery_result_is_explicitly_heuristic(self) -> None:
        result = migrated_artifact(json.loads(
            analysis_path("residue_two_b20_self_renewal_beam_result.json").read_text()
        ))
        self.assertFalse(result["claim"]["exact"])
        self.assertFalse(result["claim"]["complete"])
        self.assertEqual(result["runs"][-1]["budgets"]["333"]["best_components"], 3)
        self.assertEqual(result["runs"][-1]["budgets"]["333"]["connected_pairs"], 0)
        self.assertGreater(result["runs"][-1]["budgets"]["335"]["connected_pairs"], 0)


if __name__ == "__main__":
    unittest.main()
