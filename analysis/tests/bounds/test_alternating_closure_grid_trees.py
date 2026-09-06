from __future__ import annotations

import random
import unittest

from analysis.bounds.alternating_closure_grid_trees import (
    AXES,
    EAST,
    SOUTH,
    WEST,
    audit_tree,
    alternating_closure,
    build_model,
    grouped_alternating_closure,
    grouped_hulls,
    exact_closed_region_balance,
    exact_hall_balance,
    exact_subset_balance,
    exhaustive_census,
    occurrence_gap_bijection_count,
    sampled_occurrence_gap_bijections,
    sampled_tree_census,
    targeted_spanning_trees,
)
from analysis.bounds.cotree_row_charge import is_tree, spanning_trees


class AlternatingClosureGridTreeTests(unittest.TestCase):
    def test_full_pruned_ledger_and_closure_invariants(self) -> None:
        tree = next(spanning_trees(3))
        for axis in AXES:
            model = build_model(3, tree, axis)
            self.assertEqual(len(model.contour), 36)
            self.assertEqual(
                len(model.tokens), 6 - len(model.reached_exit_ports)
            )
            self.assertEqual(
                len(model.collisions),
                len(model.tokens) - len({source.component for source in model.tokens}),
            )
            self.assertFalse(
                any(owner.kind == "internal-token" for owner in model.reserved_owner.values())
            )
            for source in model.collisions:
                neighborhood, owners = alternating_closure(model, (source,))
                self.assertTrue(neighborhood <= model.residual_resources)
                self.assertTrue(owners)

    def test_all_n3_trees_and_all_source_subsets(self) -> None:
        result = exhaustive_census(3)
        self.assertEqual(result["tree_count"], 192)
        self.assertEqual(result["axis_audits"], 384)
        self.assertTrue(result["all_source_subsets_tested"])
        self.assertEqual(result["gap_choice_count"], 393)
        self.assertEqual(result["axis_audits_holding_for_all_gap_choices"], 384)
        self.assertEqual(result["axis_audits_holding_for_some_gap_choices"], 384)

    def test_subset_checker_agrees_with_explicit_enumeration(self) -> None:
        for tree in spanning_trees(3):
            model = build_model(3, tree, "rows")
            if model.collisions:
                hull = next(grouped_hulls(model))
                failure = exact_subset_balance(hull)
                if failure is not None:
                    self.assertLess(len(failure.neighborhood), len(failure.sources))
                self.assertEqual(failure, exact_hall_balance(hull))
                self.assertEqual(failure, exact_closed_region_balance(hull))
                return
        self.fail("expected an n=3 tree with a repeated carrier")

    def test_exact_matching_agrees_with_subset_enumeration(self) -> None:
        checked = 0
        failure_checked = False
        for tree in spanning_trees(3):
            for axis in AXES:
                for hull in grouped_hulls(build_model(3, tree, axis)):
                    self.assertEqual(
                        exact_hall_balance(hull, method="subsets"),
                        exact_hall_balance(hull, method="matching"),
                    )
                    subset_failure = exact_hall_balance(
                        hull, method="subsets", displace=False
                    )
                    matching_failure = exact_hall_balance(
                        hull, method="matching", displace=False
                    )
                    self.assertEqual(
                        subset_failure is None, matching_failure is None
                    )
                    if matching_failure is not None:
                        self.assertLess(
                            len(matching_failure.neighborhood),
                            len(matching_failure.sources),
                        )
                        failure_checked = True
                    checked += 1
            if checked >= 20 and failure_checked:
                break
        self.assertGreaterEqual(checked, 20)
        self.assertTrue(failure_checked)

    def test_sampled_gap_bijections_are_distinct_and_reproducible(self) -> None:
        tree = (
            (0, 1), (0, 4), (1, 2), (1, 5), (2, 3), (2, 6), (3, 7),
            (7, 11), (8, 12), (9, 13), (10, 14), (11, 15), (12, 13),
            (13, 14), (14, 15),
        )
        model = build_model(4, tree, "columns")
        self.assertEqual(occurrence_gap_bijection_count(model), 6)
        first = tuple(sampled_occurrence_gap_bijections(model, 4, random.Random(17)))
        second = tuple(sampled_occurrence_gap_bijections(model, 4, random.Random(17)))
        self.assertEqual(first, second)
        self.assertEqual(len({tuple(sorted(choice.items())) for choice in first}), 4)

    def test_n5_random_targeted_search_smoke(self) -> None:
        targets = targeted_spanning_trees(5, 8, random.Random(5))
        self.assertEqual(len(targets), 8)
        self.assertTrue(all(is_tree(25, tree) for _kind, tree in targets))
        result = sampled_tree_census(
            5,
            random_count=1,
            targeted_count=2,
            seed=5,
            all_gap_limit=1,
            sampled_gap_count=1,
            subset_limit=-1,
        )
        self.assertEqual(result["axis_audits"], 6)
        self.assertEqual(result["exact_matching_audits"], 6)
        self.assertEqual(result["hall_failure_count"], 0)

    def test_n4_explicit_grouped_accounting_regression(self) -> None:
        tree = (
            (0, 1), (0, 4), (1, 2), (1, 5), (2, 3), (2, 6), (3, 7),
            (5, 9), (8, 12), (9, 13), (10, 14), (11, 15), (12, 13),
            (13, 14), (14, 15),
        )
        hulls = tuple(grouped_hulls(build_model(4, tree, "rows")))
        self.assertEqual(len(hulls), 2)
        for hull in hulls:
            neighborhoods = {
                source.kind: grouped_alternating_closure(hull, (source,))[0]
                for source in hull.sources
            }
            self.assertEqual(
                hull.base.fundamental_exchanges[(5, 9)],
                ((4, 8), (6, 10), (7, 11)),
            )
            self.assertEqual(
                neighborhoods["outer"],
                {("internal", (5, 9)), ("port", (11, EAST))},
            )
            self.assertEqual(
                neighborhoods["root"],
                {("internal", (5, 9)), ("port", (11, EAST))},
            )
            self.assertIsNone(exact_hall_balance(hull))

    def test_component_is_one_resource_with_all_boundary_contacts(self) -> None:
        tree = (
            (0, 1), (0, 4), (1, 2), (1, 5), (2, 3), (2, 6), (3, 7),
            (4, 8), (7, 11), (8, 9), (8, 12), (10, 14), (11, 15),
            (13, 14), (14, 15),
        )
        hull = next(grouped_hulls(build_model(4, tree, "columns")))
        self.assertEqual(
            tuple(contact.edge for contact in hull.base.component_contacts[14]),
            ((10, 14), (11, 15), (13, 14)),
        )
        neighborhood, _owners = grouped_alternating_closure(
            hull, tuple(source for source in hull.sources if source.kind == "branch")
        )
        self.assertIn(("component", 14), neighborhood)
        self.assertIn(("port", (11, EAST)), neighborhood)
        self.assertFalse(any(resource[0] == "contact" for resource in neighborhood))

    def test_contact_local_boundary_continuation_removes_former_failure(self) -> None:
        tree = (
            (0, 1), (0, 4), (1, 2), (1, 5), (2, 3), (2, 6), (3, 7),
            (5, 9), (8, 12), (9, 13), (10, 14), (11, 15), (12, 13),
            (13, 14), (14, 15),
        )
        audit = audit_tree(4, tree, "columns")
        self.assertTrue(audit.hall_holds_for_all_gap_choices)
        self.assertIsNone(audit.hall_failure)

    def test_two_root_reverse_continuation_exposes_internal_edge(self) -> None:
        tree = (
            (0, 1), (0, 4), (1, 2), (1, 5), (2, 3), (2, 6), (3, 7),
            (4, 8), (5, 9), (8, 12), (9, 10), (10, 11), (11, 15),
            (12, 13), (14, 15),
        )
        hull = next(grouped_hulls(build_model(4, tree, "columns")))
        roots = tuple(source for source in hull.sources if source.kind == "root")
        self.assertEqual(len(roots), 2)
        root = next(source for source in roots if source.label == ("port", (13, SOUTH)))

        neighborhood, _owners = grouped_alternating_closure(hull, (root,))

        self.assertIn(("internal", (5, 9)), neighborhood)
        self.assertEqual(tuple(hull.root_reverse_seeds), roots)

    def test_T780_internal_edge_passes_to_port_11_east(self) -> None:
        tree = (
            (0, 1), (0, 4), (1, 2), (1, 5), (2, 3), (2, 6), (3, 7),
            (7, 11), (8, 12), (9, 13), (10, 14), (11, 15), (12, 13),
            (13, 14), (14, 15),
        )
        hulls = tuple(grouped_hulls(build_model(4, tree, "columns")))
        self.assertEqual(len(hulls), 6)
        for hull in hulls:
            for source in hull.sources:
                neighborhood, _owners = grouped_alternating_closure(hull, (source,))
                self.assertEqual(
                    neighborhood,
                    {
                        ("internal", (7, 11)),
                        ("port", (8, WEST)),
                        ("port", (11, EAST)),
                    },
                )
            self.assertIsNone(exact_hall_balance(hull))

    def test_T779_row_axis_has_one_outer_source_paid_by_component_11(self) -> None:
        tree = (
            (0, 1), (0, 4), (1, 2), (1, 5), (2, 3), (2, 6), (3, 7),
            (7, 11), (8, 12), (9, 13), (10, 11), (11, 15), (12, 13),
            (13, 14), (14, 15),
        )
        hulls = tuple(grouped_hulls(build_model(4, tree, "rows")))
        self.assertEqual(len(hulls), 1)
        self.assertEqual(len(hulls[0].sources), 1)
        source = hulls[0].sources[0]
        self.assertEqual(source.kind, "outer")
        self.assertEqual(source.label.component, 12)
        self.assertEqual(
            grouped_alternating_closure(hulls[0], (source,))[0],
            {("component", 11)},
        )
        self.assertIsNone(exact_hall_balance(hulls[0]))

    def test_T779_component_contact_basis_exchange_reaches_component_12(self) -> None:
        tree = (
            (0, 1), (0, 4), (1, 2), (1, 5), (2, 3), (2, 6), (3, 7),
            (7, 11), (8, 12), (9, 13), (10, 11), (11, 15), (12, 13),
            (13, 14), (14, 15),
        )
        hulls = tuple(grouped_hulls(build_model(4, tree, "columns")))
        self.assertEqual(len(hulls), 6)
        for hull in hulls:
            self.assertEqual(
                hull.base.residual_resources,
                {
                    ("component", 12),
                    ("port", (8, WEST)),
                    ("port", (14, SOUTH)),
                },
            )
            for source in hull.sources:
                neighborhood, _owners = grouped_alternating_closure(hull, (source,))
                self.assertEqual(neighborhood, hull.base.residual_resources)
            self.assertIsNone(exact_hall_balance(hull))

    def test_outer_walk_remains_ordered_during_reverse_root_continuation(self) -> None:
        tree = (
            (0, 1), (0, 3), (1, 2), (1, 4),
            (2, 5), (3, 6), (5, 8), (7, 8),
        )
        hull = next(grouped_hulls(build_model(3, tree, "columns")))
        root = next(source for source in hull.sources if source.kind == "root")
        neighborhood, owners = grouped_alternating_closure(hull, (root,))
        self.assertIn(("port", (7, SOUTH)), neighborhood)
        # The west port is reached inward through the root's descendant hull,
        # not by broadening OUT into one candidate region.
        self.assertIn(("port", (3, WEST)), neighborhood)
        self.assertEqual(
            sum(owner.kind == "exit" for owner in owners),
            3,
        )

    def test_fundamental_exchanges_are_exact_tree_basis_exchanges(self) -> None:
        tree = next(spanning_trees(3))
        model = build_model(3, tree, "rows")
        tree_set = set(model.tree)
        for tree_edge, omitted_edges in model.fundamental_exchanges.items():
            reduced = tree_set - {tree_edge}
            reached = {tree_edge[0]}
            while True:
                expanded = reached | {
                    right if left in reached else left
                    for left, right in reduced
                    if (left in reached) != (right in reached)
                }
                if expanded == reached:
                    break
                reached = expanded
            expected = tuple(sorted(
                edge for edge in model.cotree
                if (edge[0] in reached) != (edge[1] in reached)
            ))
            self.assertEqual(omitted_edges, expected)

    def test_all_n4_trees_and_all_source_subsets(self) -> None:
        result = exhaustive_census(4)
        self.assertEqual(result["tree_count"], 100_352)
        self.assertEqual(result["axis_audits"], 200_704)
        self.assertTrue(result["all_source_subsets_tested"])
        self.assertEqual(result["gap_choice_count"], 204_179)
        self.assertEqual(result["axis_audits_holding_for_all_gap_choices"], 200_704)
        self.assertEqual(result["axis_audits_holding_for_some_gap_choices"], 200_704)
        self.assertEqual(result["axis_audits_failing_for_at_least_one_gap_choice"], 0)
        self.assertEqual(result["axis_audits_failing_for_every_gap_choice"], 0)
        self.assertEqual(result["hall_counterexamples"], [])
        self.assertEqual(result["trees_with_no_axis_failing_for_every_gap_choice"], 100_352)
        self.assertEqual(result["trees_with_exactly_one_axis_failing_for_every_gap_choice"], 0)
        self.assertEqual(result["trees_with_both_axes_failing_for_every_gap_choice"], 0)
        self.assertEqual(result["trees_with_adaptive_axis_holding_for_all_gap_choices"], 100_352)
        self.assertIsNone(result["hall_counterexample"])
        self.assertIsNone(result["candidate_closed_region_counterexample"])


if __name__ == "__main__":
    unittest.main()
