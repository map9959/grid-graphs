from __future__ import annotations

import unittest

from analysis.bounds.bundle_cycle_defect_census import (
    acyclic_sets,
    adversarial_maximal_witnesses,
    defect_profile,
    independent_global_counts,
    maximal_profiles,
    row_grammar_accepts,
)


class BundleCycleDefectCensusTests(unittest.TestCase):
    def test_exact_profile_and_identities(self) -> None:
        # One of the four maximum 2 by 2 forests, with connected U.
        profile = defect_profile(2, (0b11, 0b00))
        self.assertEqual(profile.forced, 2)
        self.assertEqual(profile.unforced, 2)
        self.assertEqual(profile.sum_defect, 2)
        self.assertEqual(profile.sum_graphic_rank, 0)
        self.assertEqual(profile.boundary_deficiency_u, 4)
        self.assertEqual(profile.forced_induced_components, 1)
        self.assertEqual(profile.unforced_induced_components, 1)
        self.assertEqual(profile.forced_graph_components, 1)
        self.assertEqual(profile.defect_distribution, (0, 2, 0, 0))
        self.assertTrue(profile.maximal)
        self.assertEqual(profile.target_margin, 0)
        self.assertEqual(profile.component_strengthened_margin, 0)

    def test_zero_defect_is_exactly_nonmaximal(self) -> None:
        profile = defect_profile(3, (0, 0, 0))
        self.assertEqual(profile.sum_defect, 0)
        self.assertEqual(profile.defect_distribution[0], 9)
        self.assertFalse(profile.maximal)

    def test_component_conventions_include_isolated_vertices_of_h(self) -> None:
        # With F empty, G[F] has no components, G[U] is connected, and H is
        # spanning but edgeless, hence has one component per grid vertex.
        rows = (0, 0, 0)
        self.assertEqual(independent_global_counts(3, rows), (12, 0, 1, 9))
        profile = defect_profile(3, rows)
        self.assertEqual(profile.forced_graph_components, 9)
        self.assertEqual(profile.component_strengthened_margin, 14)

        # Empty U has zero induced components (the n=1 exceptional case is not
        # in the conjecture's n>=2 domain).
        self.assertEqual(independent_global_counts(1, (1,)), (0, 1, 0, 1))
        self.assertEqual(defect_profile(1, (1,)).component_strengthened_margin, -2)

    def test_surviving_inequality_on_complete_small_census(self) -> None:
        counts = []
        for n in range(2, 5):
            profiles = [profile for _rows, profile in maximal_profiles(n)]
            counts.append(len(profiles))
            self.assertTrue(
                all(profile.component_strengthened_margin >= 0 for profile in profiles)
            )
        self.assertEqual(counts, [4, 26, 138])

    def test_every_acyclic_set_through_five(self) -> None:
        expected = {
            2: (9, 0, 4),
            3: (100, 2, 0),
            4: (2278, 0, 14),
            5: (116252, 3, 0),
        }
        for n, (count, minimum, equalities) in expected.items():
            margins = [
                defect_profile(n, rows).component_strengthened_margin
                for rows in acyclic_sets(n)
            ]
            self.assertEqual((len(margins), min(margins), margins.count(0)),
                             (count, minimum, equalities))

    def test_adversarial_mutator_returns_dually_checked_maximal_sets(self) -> None:
        samples = adversarial_maximal_witnesses(6, attempts=4, seed=7)
        self.assertTrue(samples)
        for rows, profile in samples:
            self.assertTrue(row_grammar_accepts(6, rows))
            self.assertTrue(profile.maximal)
            self.assertGreaterEqual(profile.component_strengthened_margin, 0)


if __name__ == "__main__":
    unittest.main()
