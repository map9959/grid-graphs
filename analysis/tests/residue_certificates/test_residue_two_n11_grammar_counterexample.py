from __future__ import annotations

import json
import unittest


from analysis.residue_certificates.residue_two_n11_grammar_counterexample import build_artifact
from analysis._paths import analysis_path
from analysis.tests._support import migrated_artifact


ARTIFACT = analysis_path("residue_two_n11_grammar_counterexample.json")


class ResidueTwoN11GrammarCounterexampleTests(unittest.TestCase):
    def test_cached_artifact_regenerates_exactly(self) -> None:
        self.assertEqual(build_artifact(), migrated_artifact(json.loads(ARTIFACT.read_text())))

    def test_only_contiguous_support_fails(self) -> None:
        artifact = build_artifact()
        self.assertEqual(artifact["scope"]["u_count"], 72)
        self.assertEqual(artifact["scope"]["charged_curvature"], 5)
        self.assertEqual(artifact["failure"]["row"], 8)
        self.assertEqual(artifact["failure"]["occupied_groups"], [1, 3])
        self.assertEqual(artifact["failure"]["missing_groups"], [2])
        self.assertEqual(
            artifact["surviving_restrictions"],
            {
                "all_packet_motifs_in_n5_n8_alphabet": True,
                "no_concurrent_packet_carriers": True,
                "maximum_face_cut_open_width": 1,
                "all_states_in_hull_carrier_local_language": True,
            },
        )


if __name__ == "__main__":
    unittest.main()
