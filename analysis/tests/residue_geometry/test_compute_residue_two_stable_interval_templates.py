from __future__ import annotations

import unittest

from analysis.residue_geometry.compute_residue_two_stable_interval_templates import (
    CAP_VARIANTS,
    DEFAULT_MAX_TEMPLATES,
    GRAMMAR_METADATA,
    KEEP,
    IntervalOperation,
    Template,
    iter_templates,
    materialize,
    search_templates,
    template_count,
)


class StableIntervalTemplateComputationTests(unittest.TestCase):
    def test_declared_grammar_count_and_order_are_exact(self) -> None:
        self.assertEqual(DEFAULT_MAX_TEMPLATES, 100_000)
        self.assertEqual(template_count(), 75_296)
        self.assertEqual(GRAMMAR_METADATA["declared_template_count"], template_count())
        iterator = iter_templates()
        first = next(iterator)
        self.assertEqual(first, Template(1, (KEEP,), 0))
        self.assertEqual(next(iterator), Template(1, (KEEP,), 1))
        self.assertEqual(len(CAP_VARIANTS), 5)

    def test_one_descriptor_materializes_stably_at_all_three_widths(self) -> None:
        template = Template(3, (
            IntervalOperation(".", 1, 1),
            KEEP,
            IntervalOperation("U", 0, 1),
        ), 17)
        for k in (7, 8, 9):
            first = materialize(template, k)
            second = materialize(template, k)
            self.assertEqual(first, second)
            self.assertEqual(len(first), 3 * k + 2)
            self.assertTrue(all(len(row) == 3 * k + 2 for row in first))

    def test_statuses_distinguish_found_complete_and_capped(self) -> None:
        templates = [Template(1, (KEEP,), mask) for mask in range(3)]
        never = lambda _template: None
        complete = search_templates(3, templates=templates, evaluator=never)
        self.assertEqual(complete["status"], "complete_no_candidate")
        self.assertTrue(complete["search"]["grammar_exhausted"])

        capped = search_templates(2, templates=templates, evaluator=never)
        self.assertEqual(capped["status"], "incomplete_due_to_cap")
        self.assertFalse(capped["complete"])

        def second(template):
            return {"template": {"mask": template.cap_variant_mask}} if template.cap_variant_mask == 1 else None

        found = search_templates(
            3,
            templates=templates,
            evaluator=second,
            replay=lambda template: {"mask": template.cap_variant_mask, "independently_replayed": True},
        )
        self.assertEqual(found["status"], "found")
        self.assertEqual(found["search"]["templates_examined"], 2)
        self.assertTrue(found["candidate"]["independent_replay"]["independently_replayed"])

    def test_cap_above_hard_limit_is_rejected(self) -> None:
        with self.assertRaisesRegex(ValueError, "between 1 and 100000"):
            search_templates(100_001, templates=())


if __name__ == "__main__":
    unittest.main()
