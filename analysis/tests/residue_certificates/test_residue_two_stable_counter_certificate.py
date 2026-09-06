from __future__ import annotations

import unittest

from analysis.patterns.diagonal_patterns import residue_two_affine_pattern
from analysis.residue_certificates.residue_two_compact_transition import structural_key, trace_observations
from analysis.residue_certificates.residue_two_stable_counter_certificate import stable_rule_certificates


class ResidueTwoStableCounterCertificateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.certificates = stable_rule_certificates()
        cls.by_rule = {
            (item.source, item.action, item.target): item for item in cls.certificates
        }

    def test_all_stable_rules_have_symbolic_counter_certificates(self) -> None:
        self.assertEqual(len(self.certificates), 19)
        self.assertEqual(
            len({(item.source, item.action) for item in self.certificates}), 19
        )

    def test_symbolic_formulas_match_every_cached_stable_observation(self) -> None:
        checked = 0
        for width in range(23, 120, 3):
            for observation in trace_observations(
                width, residue_two_affine_pattern(width)
            ):
                certificate = self.by_rule[structural_key(observation)]
                length = observation.packet_length
                expected = certificate.deltas
                self.assertEqual(expected.u.at(length), observation.deltas.u)
                self.assertEqual(
                    expected.cycles.at(length), observation.deltas.cycles
                )
                self.assertEqual(expected.row.at(length), observation.deltas.row)
                self.assertEqual(expected.length.at(length), observation.deltas.length)
                checked += 1
        self.assertEqual(checked, sum(range(23, 120, 3)))


if __name__ == "__main__":
    unittest.main()
