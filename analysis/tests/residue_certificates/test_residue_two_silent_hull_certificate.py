from __future__ import annotations

import json
import unittest


from analysis.residue_certificates.residue_two_silent_hull_certificate import build_artifact
from analysis._paths import analysis_path
from analysis.tests._support import migrated_artifact


ARTIFACT = analysis_path("residue_two_silent_hull_certificate.json")


class ResidueTwoSilentHullCertificateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.cached = migrated_artifact(json.loads(ARTIFACT.read_text()))

    def test_cached_artifact_has_exact_scopes_and_terminal_five(self) -> None:
        self.assertFalse(self.cached["scope"]["arbitrary_width_K_le_2_coverage_proved"])
        self.assertTrue(self.cached["scope"]["bounded_symbolic_transition_soundness_proved"])
        self.assertFalse(self.cached["scope"]["arbitrary_word_transition_closure_proved"])
        self.assertFalse(self.cached["scope"]["universal_terminal_bound_proved"])
        self.assertEqual(self.cached["n11_silent_gap"]["silent_carrier_rows"], [8])
        certificate = self.cached["integer_min_plus_certificate"]
        self.assertEqual(certificate["terminal_constant"], 5)
        self.assertEqual(set(certificate["slack_histogram"]), {"0"})
        self.assertIn("independently", self.cached["uncovered_exact_lemma"]["terminal_sublemma"])

    def test_artifact_is_fresh(self) -> None:
        self.assertEqual(build_artifact(), self.cached)


if __name__ == "__main__":
    unittest.main()
