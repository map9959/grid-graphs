from __future__ import annotations

import unittest
from math import comb

from analysis.transport.open_slab_repair_search import build_certificate


class OpenSlabRepairTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.certificate = build_certificate()

    def test_bounded_exchange_search_is_exactly_negative(self) -> None:
        for sample in self.certificate["samples"]:
            box = sample["balanced_local_exchange_census"]["box"]
            records = sample["balanced_local_exchange_census"]["records"]
            expected = [
                comb(box["U_cells"], size) * comb(box["full_cells"], size)
                for size in range(3)
            ]
            self.assertEqual([record["tested"] for record in records], expected)
            self.assertEqual(
                [record["exact_straight_interfaces"] for record in records],
                [0, 0, 0],
            )
            self.assertTrue(sample["target_forest_completable"])
        self.assertEqual(
            sum(
                sample["closest_sample_symmetry_multiplicity"]
                for sample in self.certificate["samples"]
            ),
            8,
        )

    def test_one_extra_port_is_necessary_and_sufficient(self) -> None:
        for sample in self.certificate["samples"]:
            census = sample["port_set_census"]
            self.assertEqual(census["equal_width_exact"], 0)
            repair = census["natural_wider_repair"]
            self.assertTrue(repair["closed"])
            self.assertTrue(repair["projects_to_source_after_extra_port_removed"])
        self.assertEqual(
            self.certificate["conclusion"],
            {
                "exact_equal_width_repair": False,
                "minimum_additional_retained_ports": 1,
                "additional_U_cost": 0,
                "repair_rule": "retain the forgotten component's sole face slot",
            },
        )


if __name__ == "__main__":
    unittest.main()
