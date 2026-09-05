from __future__ import annotations

import unittest

from census_residue_two_affine_endpoint_extensions import (
    SCHEMA,
    build_report,
    census_k,
    endpoint_chains,
    replay_endpoint,
)


class ResidueTwoAffineEndpointExtensionTests(unittest.TestCase):
    def test_every_width_exhausts_two_endpoints_per_interval(self) -> None:
        for k in (7, 8, 9):
            with self.subTest(k=k):
                record = census_k(k)
                self.assertEqual(record["endpoint_type_count"], 8 * k)
                self.assertEqual(sum(record["terminal_histogram"].values()), 8 * k)
                self.assertEqual(record["status"], "all_endpoint_types_obstructed")
                self.assertNotIn("realization", record["terminal_histogram"])

    def test_all_fifty_six_transported_source_types_are_obstructed(self) -> None:
        chains = endpoint_chains()
        self.assertEqual(len(chains), 56)
        self.assertTrue(all(chain["status"] == "obstructed" for chain in chains))

    def test_terminal_samples_replay_exactly(self) -> None:
        for k in (7, 8, 9):
            for sample in census_k(k)["first_replay_by_terminal_status"].values():
                replay = replay_endpoint(k, sample["component"], sample["side"])
                self.assertEqual(replay, sample)

    def test_exact_obstruction_histograms(self) -> None:
        self.assertEqual(census_k(7)["terminal_histogram"], {
            "component_merge_or_split": 5,
            "forbidden_unit_cell": 25,
            "ray_contains_old_preserved_vertex": 22,
            "ray_out_of_grid": 4,
        })
        self.assertEqual(census_k(8)["terminal_histogram"], {
            "forbidden_unit_cell": 19,
            "ray_contains_old_preserved_vertex": 27,
            "ray_out_of_grid": 18,
        })
        self.assertEqual(census_k(9)["terminal_histogram"], {
            "forbidden_unit_cell": 10,
            "ray_contains_old_preserved_vertex": 41,
            "ray_out_of_grid": 21,
        })

    def test_report_separates_count_identity_from_geometry(self) -> None:
        report = build_report()
        self.assertEqual(report["schema"], SCHEMA)
        self.assertEqual(report["status"], "complete_endpoint_type_obstruction")
        self.assertEqual(report["surviving_chain_count"], 0)
        self.assertEqual(report["next_topology"]["name"], "two-interval endpoint-slide")


if __name__ == "__main__":
    unittest.main()
