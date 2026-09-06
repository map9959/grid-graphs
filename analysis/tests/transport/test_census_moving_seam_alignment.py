from __future__ import annotations

import unittest
from dataclasses import replace

from analysis.patterns.diagonal_patterns import (
    residue_two_affine_pattern,
    residue_two_pattern,
)
from analysis.transport.census_moving_seam_alignment import (
    PHASE_FRONT_WITNESS,
    census_known_pairs,
    d4_orientations,
    find_alignment,
    load_square_pattern,
    replay_alignment,
    row_alignment_census,
)


def widened_row(source: str, seam: int, packet: str = "UUU") -> str:
    start = 1 + 3 * seam
    return source[:start] + packet + source[start:]


class MovingSeamUnitTests(unittest.TestCase):
    def test_packet_deletion_and_radius_zero_exterior(self) -> None:
        source = ".U.U."
        target = widened_row(source, 0)
        census = row_alignment_census(source, target, seam=0, radius=0)

        self.assertIsNotNone(census)
        assert census is not None
        self.assertEqual(census.inserted_u, 3)
        self.assertEqual(census.aligned_rewrites, 0)
        self.assertEqual(census.exterior_cells, 5)
        self.assertIsNone(row_alignment_census(source, target, seam=1, radius=0))

        rewritten_neighbor = target[:4] + ("U" if target[4] == "." else ".") + target[5:]
        self.assertIsNone(row_alignment_census(source, rewritten_neighbor, seam=0, radius=0))
        radius_one = row_alignment_census(source, rewritten_neighbor, seam=0, radius=1)
        self.assertIsNotNone(radius_one)
        assert radius_one is not None
        self.assertEqual(radius_one.aligned_rewrites, 1)

    def test_boundary_policy_is_explicit_and_counted_separately(self) -> None:
        source = ".U.UU"
        widened = widened_row(source, 0)
        target = "U" + widened[1:-1] + "."
        self.assertIsNone(row_alignment_census(source, target, seam=0, radius=10))

        census = row_alignment_census(
            source,
            target,
            seam=0,
            radius=10,
            allow_boundary_rewrites=True,
        )
        self.assertIsNotNone(census)
        assert census is not None
        self.assertEqual(census.boundary_rewrites, 2)
        self.assertEqual(census.boundary_rewrites_to_u, 1)
        self.assertEqual(census.boundary_rewrites_to_dot, 1)
        self.assertEqual(census.aligned_rewrites, 0)

    def test_seam_may_move_only_one_packet_per_target_row(self) -> None:
        source = ["." * 8] * 8
        smooth = [0, 0, 1, 2, 2, 1, 0, 0, 1, 1, 0]
        smooth_target = [widened_row(source[0], seam) for seam in smooth]
        self.assertIsNotNone(find_alignment(source, smooth_target, radius=0))

        jumping = list(smooth)
        jumping[2] = 2
        jumping_target = [widened_row(source[0], seam) for seam in jumping]
        self.assertIsNone(find_alignment(source, jumping_target, radius=0))

    def test_complete_path_has_exactly_three_holds_and_replays(self) -> None:
        source = ["." * 5] * 5
        target = ["." * 8] * 8
        alignment = find_alignment(source, target, radius=0)

        self.assertIsNotNone(alignment)
        assert alignment is not None
        self.assertEqual(sum(step.operation == "HOLD" for step in alignment.steps), 3)
        self.assertEqual(sum(step.operation == "ADVANCE" for step in alignment.steps), 5)
        correspondence = [step.source_row for step in alignment.steps]
        self.assertEqual(correspondence, sorted(correspondence))
        self.assertEqual(set(correspondence), set(range(5)))
        totals = replay_alignment(source, target, alignment)
        self.assertEqual(totals["inserted_dot"], 24)

    def test_replay_rejects_hold_before_advance_and_backward_hold(self) -> None:
        source = ["." * 5] * 5
        target = ["." * 8] * 8
        alignment = find_alignment(source, target, radius=0)
        assert alignment is not None

        steps = list(alignment.steps)
        steps[0] = replace(steps[0], operation="HOLD")
        with self.assertRaisesRegex(ValueError, "unavailable"):
            replay_alignment(source, target, replace(alignment, steps=tuple(steps)))

        hold_index = next(index for index, step in enumerate(alignment.steps) if step.operation == "HOLD")
        steps = list(alignment.steps)
        steps[hold_index] = replace(steps[hold_index], source_row=3)
        with self.assertRaisesRegex(ValueError, "unavailable"):
            replay_alignment(source, target, replace(alignment, steps=tuple(steps)))

    def test_replay_rejects_a_seam_jump(self) -> None:
        source = ["." * 8] * 8
        target = ["." * 11] * 11
        alignment = find_alignment(source, target, radius=0)
        assert alignment is not None
        steps = list(alignment.steps)
        steps[1] = replace(steps[1], seam=2)
        invalid = replace(alignment, steps=tuple(steps))
        with self.assertRaisesRegex(ValueError, "more than one"):
            replay_alignment(source, target, invalid)

    def test_d4_images_are_deduplicated_with_action_aliases(self) -> None:
        symmetric = d4_orientations(["...", "...", "..."])
        self.assertEqual(len(symmetric), 1)
        self.assertEqual(len(symmetric[0].aliases), 8)

        asymmetric = d4_orientations(["U..", "UU.", "..."])
        self.assertEqual(len(asymmetric), 8)
        self.assertEqual(asymmetric[0].name, "rotate_0")


class KnownPairCensusTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.record = census_known_pairs()

    def test_known_minimum_radii_and_counts(self) -> None:
        pairs = {pair["label"]: pair for pair in self.record["pairs"]}
        self.assertEqual(pairs["exact-8-to-exact-11"]["minimum_radius"], 1)
        self.assertEqual(pairs["exact-11-to-exact-14"]["minimum_radius"], 1)
        self.assertEqual(pairs["exact-14-to-affine-17"]["minimum_radius"], 1)
        affine = pairs["affine-17-to-phase-front-20"]
        self.assertEqual(affine["minimum_radius"], 3)
        self.assertEqual((affine["source"]["u_cells"], affine["target"]["u_cells"]), (179, 250))
        self.assertEqual([item["works"] for item in affine["radii"]], [False, False, False, True, True, True, True])

    def test_all_minimum_certificates_are_stable_and_replayable(self) -> None:
        patterns = [
            (residue_two_pattern(8), residue_two_pattern(11)),
            (residue_two_pattern(11), residue_two_pattern(14)),
            (residue_two_pattern(14), residue_two_affine_pattern(17)),
            (residue_two_affine_pattern(17), load_square_pattern(PHASE_FRONT_WITNESS)),
        ]
        expected = [
            {
                "orientations": ("rotate_0", "rotate_0"),
                "holds": [(8, 7), (9, 7), (10, 7)],
                "seams": [0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0],
                "rewrites": (18, 4, 23, 10),
            },
            {
                "orientations": ("rotate_90", "rotate_0_reflect_lr"),
                "holds": [(2, 1), (3, 1), (12, 9)],
                "seams": [2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 2, 1, 0],
                "rewrites": (19, 4, 31, 11),
            },
            {
                "orientations": ("rotate_0", "rotate_0"),
                "holds": [(12, 11), (13, 11), (14, 11)],
                "seams": [0, 0, 0, 1, 2, 2, 3, 3, 3, 3, 3, 3, 2, 3, 2, 1, 0],
                "rewrites": (21, 0, 40, 11),
            },
            {
                "orientations": ("rotate_0", "rotate_0"),
                "holds": [(17, 16), (18, 16), (19, 16)],
                "seams": [0, 0, 0, 0, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1],
                "rewrites": (100, 0, 47, 13),
            },
        ]
        for pair, (source, target), stable in zip(
            self.record["pairs"], patterns, expected, strict=True
        ):
            match = pair["radii"][pair["minimum_radius"]]["alignment"]
            self.assertEqual(
                (match["source_orientation"], match["target_orientation"]),
                stable["orientations"],
            )
            self.assertEqual(
                [(item["target_row"], item["source_row"]) for item in match["hold_rows"]],
                stable["holds"],
            )
            self.assertEqual(match["seam_schedule"], stable["seams"])
            census = match["rewrite_census"]
            self.assertEqual(
                (
                    census["aligned_rewrites"],
                    census["boundary_rewrites"],
                    census["inserted_u"],
                    census["inserted_dot"],
                ),
                stable["rewrites"],
            )

            source_rows = next(
                item.rows for item in d4_orientations(source)
                if item.name == match["source_orientation"]
            )
            target_rows = next(
                item.rows for item in d4_orientations(target)
                if item.name == match["target_orientation"]
            )
            alignment = find_alignment(
                source_rows,
                target_rows,
                pair["minimum_radius"],
                allow_boundary_rewrites=True,
                source_orientation=match["source_orientation"],
                target_orientation=match["target_orientation"],
            )
            self.assertIsNotNone(alignment)
            assert alignment is not None
            self.assertEqual(replay_alignment(source_rows, target_rows, alignment), census)


if __name__ == "__main__":
    unittest.main()
