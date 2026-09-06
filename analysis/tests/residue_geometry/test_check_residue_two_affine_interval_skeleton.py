from __future__ import annotations

import unittest

from analysis.residue_geometry.check_residue_two_affine_interval_skeleton import (
    SCHEMA,
    analyze_k,
    analyze_transition,
    build_report,
)


class ResidueTwoAffineIntervalSkeletonTests(unittest.TestCase):
    def test_k7_interval_star_certificate(self) -> None:
        record = analyze_k(7)

        self.assertEqual(record["status"], "verified")
        self.assertTrue(all(record["checks"].values()))
        self.assertEqual(record["claims"]["component_count"]["observed"], 28)
        self.assertEqual(record["claims"]["preserved_count"]["observed"], 194)
        self.assertEqual(record["claims"]["incidence_links"]["observed"], 27)
        self.assertTrue(record["physical_attachment_graph"]["tree"])
        self.assertEqual(len(record["leaf_elimination_order"]), 28)
        self.assertLessEqual(
            max(record["leaf_elimination_suffix_intersection_sizes"]), 1
        )

    def test_report_records_exact_observed_formulas(self) -> None:
        report = build_report()

        self.assertEqual(report["status"], "verified")
        self.assertEqual(
            report["observed_formulas"]["component_count"]["observed_formula"],
            "4k",
        )
        self.assertEqual(
            report["observed_formulas"]["preserved_count"]["observed_formula"],
            "3k^2 + 6k + 5",
        )
        self.assertEqual(
            report["observed_formulas"]["incidence_links"]["observed_formula"],
            "4k - 1",
        )

    def test_symbolic_nodes_have_canonical_root_and_physical_parents(self) -> None:
        skeleton = analyze_k(7)["rooted_symbolic_skeleton"]

        self.assertEqual(skeleton["root"], "H:r0:c2..22")
        self.assertEqual(len(skeleton["nodes"]), 28)
        self.assertEqual(skeleton["nodes"][0]["parent"], None)
        self.assertEqual(skeleton["nodes"][0]["physical_parent_attachment"], None)
        self.assertTrue(all(
            node["parent"] is not None and node["physical_parent_attachment"] is not None
            for node in skeleton["nodes"][1:]
        ))

    def test_k7_k8_k9_affine_transitions_have_exact_symbolic_recurrence(self) -> None:
        for k in (7, 8, 9):
            with self.subTest(k=k):
                transition = analyze_transition(k)
                recurrence = transition["count_recurrence"]

                self.assertEqual(transition["status"], "verified")
                self.assertTrue(all(transition["checks"].values()))
                self.assertEqual(recurrence["old_node_count"], 4 * k)
                self.assertEqual(recurrence["new_node_count"], 4)
                self.assertEqual(recurrence["changed_node_count"], k + 2)
                self.assertEqual(recurrence["old_node_length_gain"], 3 * k + 6)
                self.assertEqual(recurrence["new_node_length_gain"], 3 * k + 3)
                self.assertEqual(recurrence["total_gain"], 6 * k + 9)
                self.assertEqual(recurrence["required_target_gain"], 6 * k + 10)
                self.assertEqual(recurrence["interface_mismatch"], -1)
                self.assertFalse(transition["old_parent_changes"])
                self.assertFalse(transition["physical_parent_attachment_mismatches"])

    def test_transition_exports_expected_new_leaves_and_owner_nonuniformity(self) -> None:
        transition = analyze_transition(7)

        self.assertEqual(
            {node["id"] for node in transition["new_nodes"]},
            {
                "H:r2:c5..5",
                "H:r12:c20..20",
                "V:c6:r4..23",
                "V:c18:r10..11",
            },
        )
        self.assertTrue(all(not node["children"] for node in transition["new_nodes"]))
        self.assertFalse(transition["nonuniformity"]["raw_owner_relation_unique"])
        self.assertEqual(transition["nonuniformity"]["ambiguous_old_node_count"], 3)

    def test_report_contains_all_requested_transition_exports(self) -> None:
        report = build_report()

        self.assertEqual(report["schema"], SCHEMA)
        self.assertEqual([item["k"] for item in report["transitions"]], [7, 8, 9])
        self.assertEqual(report["status"], "verified")


if __name__ == "__main__":
    unittest.main()
