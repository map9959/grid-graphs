from __future__ import annotations

import json
import unittest
from dataclasses import replace
from itertools import product

from analysis._paths import analysis_path
from analysis.patterns.diagonal_patterns import (
    residue_two_affine_pattern,
    residue_two_pattern,
)
from analysis.searches.search_residue_two_moving_seam import (
    PACKET_ALPHABET,
    AlignmentAutomaton,
    AlignmentState,
    AlignmentTransition,
    CompatibleSchedule,
    Node,
    PathStep,
    ScheduleTemplate,
    affine_compatible_schedule,
    affine_holds_compatible_schedule,
    affine_one_hold_relocation_schedule,
    affine_schedule_template,
    affine_two_hold_relocation_schedule,
    build_alignment_automaton,
    build_bidirectional_frontiers,
    compatible_schedule_automaton,
    compatible_schedule_for_operation_word,
    compatible_schedule_operation_word_shards,
    complete_operation_words,
    enumerate_domain_rows,
    exact_state_key,
    holds_compatible_schedule_automaton,
    join_bidirectional_frontiers,
    language_membership,
    one_hold_relocation_schedule_automaton,
    replay_path,
    row_boundary_variants,
    row_domain_variants,
    row_packet_domains,
    schedule_accepts_steps,
    search,
    search_bidirectional,
)
from analysis.tests._support import migrated_artifact, slow_test
from analysis.tiles.tile_grammar import (
    FrontierState,
    advance_row,
    initial_state,
    row_mask,
    stream_row_packets,
)
from analysis.transport.census_moving_seam_alignment import row_alignment_census


class MovingSeamSearchTests(unittest.TestCase):
    def test_recorded_result_distinguishes_complete_and_incomplete_scopes(self) -> None:
        record = migrated_artifact(json.loads(
            analysis_path("residue_two_moving_seam_result.json").read_text()
        ))
        complete = {
            (item["schedule"], item["u_limit"]): item
            for item in record["complete_searches"]
        }
        self.assertEqual(complete[("affine", 178)]["connected_pairs"], 0)
        self.assertEqual(
            complete[("affine-holds-compatible", 178)]["cost_feasible_pairs"],
            817914,
        )
        self.assertGreater(
            complete[("affine-holds-compatible", 179)]["connected_pairs"], 0
        )
        self.assertEqual(
            complete[("affine-one-hold-relocation", 178)]["cost_feasible_pairs"],
            1807842,
        )
        self.assertEqual(
            complete[("affine-one-hold-relocation", 178)]["connected_pairs"], 0
        )
        self.assertEqual(
            complete[("affine-two-hold-relocation", 178)]["cost_feasible_pairs"],
            4256057,
        )
        self.assertEqual(
            complete[("affine-two-hold-relocation", 178)]["connected_pairs"], 0
        )
        self.assertGreater(
            complete[("affine-two-hold-relocation", 179)]["connected_pairs"], 0
        )
        boundary = [
            item
            for item in record["complete_searches"]
            if item["schedule"] == "affine"
            and item.get("boundary_rewrite_budget") == 1
        ]
        self.assertEqual({item["u_limit"] for item in boundary}, {178, 179})
        self.assertEqual(
            next(item for item in boundary if item["u_limit"] == 178)["connected_pairs"],
            0,
        )
        self.assertGreater(
            next(item for item in boundary if item["u_limit"] == 179)["connected_pairs"],
            0,
        )
        self.assertTrue(
            all(
                item["conclusion"] == "INCOMPLETE"
                for item in record["incomplete_searches"]
            )
        )

    def test_generated_domains_equal_direct_compatibility(self) -> None:
        source = ".U..U"
        for seam in range(2):
            for radius in (0, 1):
                generated = enumerate_domain_rows(source, seam, radius)
                direct = {
                    "." + "".join(bits) + "U"
                    for bits in product(PACKET_ALPHABET.values(), repeat=2)
                    if row_alignment_census(
                        source, "." + "".join(bits) + "U", seam, radius
                    )
                    is not None
                }
                self.assertEqual(generated, direct)

    def test_boundary_variants_equal_brute_enumeration(self) -> None:
        for source in (".UUU.", "UUUUU"):
            for budget in (0, 1):
                expected = {
                    (left, right, (left != source[0]) + (right != source[-1]))
                    for left, right in product(".U", repeat=2)
                    if (left != source[0]) + (right != source[-1]) <= budget
                }
                self.assertEqual(
                    set(row_boundary_variants(source, boundary_rewrites=budget)),
                    expected,
                )

            fixed = "U" + "." * 6 + "U"
            expected_delta = (fixed[0] != source[0]) + (fixed[-1] != source[-1])
            variants = row_domain_variants(
                source,
                seam=0,
                radius=1,
                fixed_row=fixed,
                boundary_rewrites=1,
            )
            self.assertEqual(
                {(left, right, delta) for left, right, _, delta in variants},
                (
                    {(fixed[0], fixed[-1], expected_delta)}
                    if expected_delta <= 1
                    else set()
                ),
            )

        source = ".UUU."
        for seam in range(2):
            for budget in (0, 1):
                expected_rows = {
                    left + "".join(packets) + right
                    for left, right in product(".U", repeat=2)
                    for packets in product(PACKET_ALPHABET.values(), repeat=2)
                    if (
                        census := row_alignment_census(
                            source,
                            left + "".join(packets) + right,
                            seam,
                            radius=1,
                            allow_boundary_rewrites=True,
                        )
                    )
                    is not None
                    and census.boundary_rewrites <= budget
                }
                self.assertEqual(
                    enumerate_domain_rows(
                        source, seam, radius=1, boundary_rewrites=budget
                    ),
                    expected_rows,
                )

    def test_replay_rejects_two_boundary_changes_at_budget_one(self) -> None:
        target = residue_two_pattern(8)
        groups = ((0,), (1,), (2, 3), (4, 5, 6), (7,))
        source = tuple(
            target[group[0]][0] + target[group[0]][4:7] + target[group[0]][-1]
            for group in groups
        )
        result = search_bidirectional(
            source=source,
            target_n=8,
            radius=1,
            u_count=100,
            cut=4,
            fixed_rows=(),
            fixed_target=target,
        )
        assert result.steps is not None and result.witness is not None
        changed = list(result.witness)
        toggle = {".": "U", "U": "."}
        for row in (0, 7):
            changed[row] = toggle[changed[row][0]] + changed[row][1:]
        with self.assertRaisesRegex(ValueError, "boundary rewrite budget"):
            replay_path(source, changed, result.steps, radius=1, boundary_rewrites=1)

    def test_streamed_transitions_equal_advance_row(self) -> None:
        after_first = advance_row(initial_state(8), row_mask(".UUUUUUU"))
        assert after_first is not None
        specification = row_packet_domains(".UUU.", seam=1, radius=0)
        assert specification is not None
        prefix, suffix, domains = specification
        for incoming in (initial_state(8), after_first):
            streamed, _ = stream_row_packets(
                incoming, prefix, suffix, domains, packet_alphabet=PACKET_ALPHABET
            )
            observed = {(item.row_mask, item.outgoing) for item in streamed}
            expected = set()
            for row in enumerate_domain_rows(".UUU.", seam=1, radius=0):
                mask = row_mask(row)
                outgoing = advance_row(incoming, mask)
                if outgoing is not None:
                    expected.add((mask, outgoing))
            self.assertEqual(observed, expected)

    def test_key_uses_full_partition_but_not_cost_or_cycles(self) -> None:
        left_state = FrontierState(8, 3, 5, (0, 1, 1), 20, 0)
        dominated_state = FrontierState(8, 3, 5, (0, 1, 1), 21, 7)
        other_partition = FrontierState(8, 3, 5, (0, 1, 2), 20, 0)
        alignment = AlignmentState(3, 0, 1)
        left = Node(left_state, alignment, None, None, None)
        dominated = Node(dominated_state, alignment, None, None, None)
        other = Node(other_partition, alignment, None, None, None)
        self.assertEqual(exact_state_key(left), exact_state_key(dominated))
        self.assertNotEqual(exact_state_key(left), exact_state_key(other))

    def test_forward_and_reverse_alignment_relations_are_identical(self) -> None:
        automaton = build_alignment_automaton()
        self.assertEqual(len(automaton.layers), 18)
        for row in range(17):
            forward = set(automaton.forward[row])
            reverse = set(automaton.reverse[row])
            self.assertEqual(forward, reverse)
            expected = set()
            for before in automaton.layers[row]:
                choices = []
                if before.cursor < 14:
                    choices.append(
                        ("ADVANCE", before.cursor, before.cursor + 1, before.holds)
                    )
                if before.cursor > 0 and before.holds < 3:
                    choices.append(
                        ("HOLD", before.cursor - 1, before.cursor, before.holds + 1)
                    )
                seams = (
                    range(5)
                    if before.previous_seam < 0
                    else range(
                        max(0, before.previous_seam - 1),
                        min(5, before.previous_seam + 2),
                    )
                )
                for operation, source_row, cursor, holds in choices:
                    for seam in seams:
                        expected.add(
                            (
                                before,
                                AlignmentState(cursor, holds, seam),
                                operation,
                                source_row,
                                seam,
                            )
                        )
            observed = {
                (edge.before, edge.after, edge.operation, edge.source_row, edge.seam)
                for edge in forward
            }
            self.assertEqual(observed, expected)

    def test_compatible_automaton_matches_independent_toy_path_enumeration(
        self,
    ) -> None:
        base = build_alignment_automaton(source_n=2, target_n=5, seams=3)
        source = ("........", "........")

        def target_row(packet: int | None) -> str:
            packets = ["...", "...", "..."]
            if packet is not None:
                packets[packet] = "UUU"
            return "." + "".join(packets) + "."

        target = tuple(target_row(packet) for packet in (2, 2, None, 0, 0))
        paths = [(base.layers[0][0], ())]
        for row in range(5):
            following = []
            for state, path in paths:
                for edge in base.forward[row]:
                    if edge.before != state:
                        continue
                    if (
                        row_alignment_census(
                            source[edge.source_row], target[row], edge.seam, radius=1
                        )
                        is not None
                    ):
                        following.append((edge.after, (*path, edge)))
            paths = following
        expected_paths = [path for state, path in paths if state in base.layers[-1]]
        expected_edges = {edge for path in expected_paths for edge in path}
        expected_states = [set() for _ in range(6)]
        for path in expected_paths:
            expected_states[0].add(path[0].before)
            for row, edge in enumerate(path):
                expected_states[row + 1].add(edge.after)

        compatible = compatible_schedule_automaton(base, source, target, 1)
        self.assertEqual(compatible.complete_path_count, len(expected_paths))
        self.assertEqual(
            {edge for layer in compatible.automaton.forward for edge in layer},
            expected_edges,
        )
        self.assertEqual(
            [set(layer) for layer in compatible.automaton.layers], expected_states
        )

    def test_affine_compatible_contains_fixed_schedule_and_target(self) -> None:
        source = residue_two_pattern(14)
        target = residue_two_affine_pattern(17)
        compatible = affine_compatible_schedule(source)
        fixed = affine_schedule_template(source)
        self.assertGreater(compatible.complete_path_count, 0)
        for row, edge in enumerate(fixed.transitions):
            self.assertIn(edge, compatible.automaton.forward[row])
        for row, edges in enumerate(compatible.automaton.forward):
            for edge in edges:
                self.assertIsNotNone(
                    row_alignment_census(
                        source[edge.source_row], target[row], edge.seam, radius=1
                    )
                )
        result = search_bidirectional(
            u_count=179,
            cut=8,
            fixed_target=target,
            schedule="affine-compatible",
        )
        self.assertEqual(result.conclusion, "SAT")
        self.assertEqual(result.witness, tuple(target))

    def test_holds_compatible_matches_independent_toy_seam_paths(self) -> None:
        source = ("........", "........")

        def target_row(packet: int | None) -> str:
            packets = ["...", "...", "..."]
            if packet is not None:
                packets[packet] = "UUU"
            return "." + "".join(packets) + "."

        target = tuple(target_row(packet) for packet in (2, 2, None, 0, 0))
        operations = (
            ("ADVANCE", 0, 1, 0),
            ("ADVANCE", 1, 2, 0),
            ("HOLD", 1, 2, 1),
            ("HOLD", 1, 2, 2),
            ("HOLD", 1, 2, 3),
        )
        fixed = []
        before = AlignmentState(0, 0, -1)
        for row, (operation, source_row, cursor, holds) in enumerate(operations):
            after = AlignmentState(cursor, holds, 1)
            fixed.append(
                AlignmentTransition(row, before, after, operation, source_row, 1)
            )
            before = after
        template = ScheduleTemplate("toy", 2, 5, 1, tuple(fixed))

        paths = [(AlignmentState(0, 0, -1), ())]
        for row, control in enumerate(template.transitions):
            following = []
            for state, path in paths:
                seams = (
                    range(3)
                    if state.previous_seam < 0
                    else range(
                        max(0, state.previous_seam - 1),
                        min(3, state.previous_seam + 2),
                    )
                )
                for seam in seams:
                    if (
                        row_alignment_census(
                            source[control.source_row], target[row], seam, radius=1
                        )
                        is None
                    ):
                        continue
                    after = AlignmentState(
                        control.after.cursor, control.after.holds, seam
                    )
                    edge = AlignmentTransition(
                        row,
                        state,
                        after,
                        control.operation,
                        control.source_row,
                        seam,
                    )
                    following.append((after, (*path, edge)))
            paths = following
        expected_paths = [path for _, path in paths]
        expected_edges = {edge for path in expected_paths for edge in path}
        compatible = holds_compatible_schedule_automaton(
            template, source, target, 1, seams=3
        )
        self.assertEqual(compatible.complete_path_count, len(expected_paths))
        self.assertEqual(
            {edge for layer in compatible.automaton.forward for edge in layer},
            expected_edges,
        )

    def test_affine_holds_compatible_contains_fixed_schedule(self) -> None:
        source = residue_two_pattern(14)
        target = residue_two_affine_pattern(17)
        fixed = affine_schedule_template(source)
        compatible = affine_holds_compatible_schedule(source)
        self.assertGreater(compatible.complete_path_count, 0)
        for row, edge in enumerate(fixed.transitions):
            self.assertIn(edge, compatible.automaton.forward[row])
        for row, edges in enumerate(compatible.automaton.forward):
            for edge in edges:
                fixed_edge = fixed.transitions[row]
                self.assertEqual(
                    (
                        edge.operation,
                        edge.source_row,
                        edge.before.cursor,
                        edge.before.holds,
                    ),
                    (
                        fixed_edge.operation,
                        fixed_edge.source_row,
                        fixed_edge.before.cursor,
                        fixed_edge.before.holds,
                    ),
                )
        result = search_bidirectional(
            u_count=179,
            cut=8,
            fixed_target=target,
            schedule="affine-holds-compatible",
        )
        self.assertEqual(result.conclusion, "SAT")
        self.assertEqual(result.witness, tuple(target))

    def test_one_hold_relocation_matches_independent_toy_enumeration(self) -> None:
        source = (".....", ".....")
        target = ("........",) * 5
        baseline_operations = ("ADVANCE", "HOLD", "HOLD", "HOLD", "ADVANCE")
        fixed = []
        before = AlignmentState(0, 0, -1)
        for row, operation in enumerate(baseline_operations):
            source_row = before.cursor if operation == "ADVANCE" else before.cursor - 1
            after = AlignmentState(
                before.cursor + (operation == "ADVANCE"),
                before.holds + (operation == "HOLD"),
                0,
            )
            fixed.append(
                AlignmentTransition(row, before, after, operation, source_row, 0)
            )
            before = after
        template = ScheduleTemplate("toy", 2, 5, 1, tuple(fixed))

        expected_paths = set()
        for removed_row in (1, 2, 3):
            for inserted_row in (0, 4):
                operations = list(baseline_operations)
                operations[removed_row] = "ADVANCE"
                operations[inserted_row] = "HOLD"
                for seams in product(range(2), repeat=5):
                    if any(
                        abs(left - right) > 1 for left, right in zip(seams, seams[1:])
                    ):
                        continue
                    cursor = holds = removals = insertions = 0
                    previous_seam = -1
                    path = []
                    valid = True
                    for row, (operation, seam) in enumerate(
                        zip(operations, seams, strict=True)
                    ):
                        if operation == "ADVANCE":
                            if cursor >= len(source):
                                valid = False
                                break
                            source_row, next_cursor = cursor, cursor + 1
                        else:
                            if cursor == 0:
                                valid = False
                                break
                            source_row, next_cursor = cursor - 1, cursor
                        removals += (
                            baseline_operations[row] == "HOLD"
                            and operation == "ADVANCE"
                        )
                        insertions += (
                            baseline_operations[row] == "ADVANCE"
                            and operation == "HOLD"
                        )
                        after = AlignmentState(
                            next_cursor,
                            holds + (operation == "HOLD"),
                            seam,
                            removals,
                            insertions,
                        )
                        before = AlignmentState(
                            cursor,
                            holds,
                            previous_seam,
                            removals
                            - (
                                baseline_operations[row] == "HOLD"
                                and operation == "ADVANCE"
                            ),
                            insertions
                            - (
                                baseline_operations[row] == "ADVANCE"
                                and operation == "HOLD"
                            ),
                        )
                        if (
                            row_alignment_census(
                                source[source_row], target[row], seam, radius=1
                            )
                            is None
                        ):
                            valid = False
                            break
                        path.append(
                            AlignmentTransition(
                                row, before, after, operation, source_row, seam
                            )
                        )
                        cursor, holds, previous_seam = next_cursor, after.holds, seam
                    if valid and (cursor, holds, removals, insertions) == (2, 3, 1, 1):
                        expected_paths.add(tuple(path))

        compatible = one_hold_relocation_schedule_automaton(
            template, source, target, 1, seams=2
        )
        observed_paths = {(())}
        for edges in compatible.automaton.forward:
            observed_paths = {
                (*path, edge)
                for path in observed_paths
                for edge in edges
                if not path or edge.before == path[-1].after
            }
        self.assertEqual(observed_paths, expected_paths)
        self.assertEqual(compatible.complete_path_count, len(expected_paths))
        self.assertEqual(
            {edge for path in observed_paths for edge in path},
            {edge for path in expected_paths for edge in path},
        )
        for row, layer in enumerate(compatible.automaton.layers):
            expected_states = {
                path[0].before if row == 0 else path[row - 1].after
                for path in expected_paths
            }
            self.assertEqual(set(layer), expected_states)
        for path in observed_paths:
            operations = tuple(edge.operation for edge in path)
            self.assertEqual(
                sum(
                    baseline == "HOLD" and operation == "ADVANCE"
                    for baseline, operation in zip(
                        baseline_operations, operations, strict=True
                    )
                ),
                1,
            )
            self.assertEqual(
                sum(
                    baseline == "ADVANCE" and operation == "HOLD"
                    for baseline, operation in zip(
                        baseline_operations, operations, strict=True
                    )
                ),
                1,
            )
            self.assertEqual(path[-1].after.baseline_hold_removals, 1)
            self.assertEqual(path[-1].after.baseline_advance_insertions, 1)

    def test_relocation_count_is_exact_on_toy(self) -> None:
        source = ("........",) * 4
        target = ("...........",) * 7
        baseline = ("ADVANCE", "ADVANCE", "HOLD", "HOLD", "HOLD", "ADVANCE", "ADVANCE")
        before = AlignmentState(0, 0, -1)
        transitions = []
        for row, operation in enumerate(baseline):
            source_row = before.cursor if operation == "ADVANCE" else before.cursor - 1
            after = AlignmentState(
                before.cursor + (operation == "ADVANCE"),
                before.holds + (operation == "HOLD"),
                0,
            )
            transitions.append(
                AlignmentTransition(row, before, after, operation, source_row, 0)
            )
            before = after
        template = ScheduleTemplate("toy-four", 4, 7, 1, tuple(transitions))

        for relocation_count in (0, 1, 2):
            expected_words = set()
            for word in product(("ADVANCE", "HOLD"), repeat=7):
                if (
                    sum(a == "HOLD" and b == "ADVANCE" for a, b in zip(baseline, word))
                    != relocation_count
                ):
                    continue
                if (
                    sum(a == "ADVANCE" and b == "HOLD" for a, b in zip(baseline, word))
                    != relocation_count
                ):
                    continue
                cursor = 0
                valid = True
                for operation in word:
                    if operation == "ADVANCE":
                        valid &= cursor < len(source)
                        cursor += 1
                    else:
                        valid &= cursor > 0
                    if not valid:
                        break
                if valid and cursor == len(source):
                    expected_words.add(word)
            schedule = one_hold_relocation_schedule_automaton(
                template,
                source,
                target,
                1,
                seams=1,
                relocation_count=relocation_count,
            )
            self.assertEqual(
                schedule.metadata["complete_operation_word_count"], len(expected_words)
            )
            self.assertEqual(schedule.complete_path_count, len(expected_words))
            for state in schedule.automaton.layers[-1]:
                self.assertEqual(state.baseline_hold_removals, relocation_count)
                self.assertEqual(state.baseline_advance_insertions, relocation_count)

    def test_affine_one_hold_relocation_is_exact_and_contains_fixed_target(
        self,
    ) -> None:
        schedule = affine_one_hold_relocation_schedule()
        baseline = tuple(
            edge.operation for edge in affine_schedule_template().transitions
        )
        words_by_state = {schedule.automaton.layers[0][0]: {()}}
        for edges in schedule.automaton.forward:
            following = {}
            for edge in edges:
                following.setdefault(edge.after, set()).update(
                    (*word, edge.operation)
                    for word in words_by_state.get(edge.before, ())
                )
            words_by_state = following
        operation_words = {word for words in words_by_state.values() for word in words}
        self.assertTrue(schedule.metadata["fixed_target_has_representation"])
        self.assertEqual(schedule.complete_path_count, 1274550)
        self.assertEqual(
            schedule.layer_state_counts,
            (1, 5, 5, 5, 4, 3, 4, 2, 3, 2, 4, 2, 1, 4, 4, 4, 5, 5),
        )
        self.assertEqual(
            schedule.layer_edge_counts,
            (5, 13, 13, 11, 8, 10, 6, 4, 5, 7, 5, 2, 4, 9, 11, 11, 13),
        )
        self.assertEqual(schedule.metadata["scope"], "exactly-one-hold-relocation")
        self.assertEqual(schedule.metadata["complete_operation_word_count"], 21)
        self.assertNotIn(baseline, operation_words)
        for state in schedule.automaton.layers[-1]:
            self.assertEqual(state.baseline_hold_removals, 1)
            self.assertEqual(state.baseline_advance_insertions, 1)
        for word in operation_words:
            self.assertEqual(
                sum(a == "HOLD" and b == "ADVANCE" for a, b in zip(baseline, word)),
                1,
            )
            self.assertEqual(
                sum(a == "ADVANCE" and b == "HOLD" for a, b in zip(baseline, word)),
                1,
            )
        result = search_bidirectional(
            u_count=179,
            cut=8,
            fixed_target=residue_two_affine_pattern(17),
            schedule=schedule,
        )
        self.assertEqual(result.conclusion, "SAT")
        self.assertEqual(result.witness, tuple(residue_two_affine_pattern(17)))

    def test_affine_one_hold_operation_word_shards_are_stable_and_disjoint(
        self,
    ) -> None:
        schedule = affine_one_hold_relocation_schedule()
        shards = compatible_schedule_operation_word_shards(schedule)
        encoded = tuple(
            "".join("A" if operation == "ADVANCE" else "H" for operation in word)
            for word in complete_operation_words(schedule)
        )
        self.assertEqual(
            encoded,
            (
                "AAAAAAAAAAAHAHHAA",
                "AAAAAAAAAAAHHAHAA",
                "AAAAAAAAAAAHHHAAA",
                "AAAAAAAAAAHAAHHAA",
                "AAAAAAAAAAHAHAHAA",
                "AAAAAAAAAAHAHHAAA",
                "AAAAAAAAAHAAAHHAA",
                "AAAAAAAAAHAAHAHAA",
                "AAAAAAAAAHAAHHAAA",
                "AAAAAAAAHAAAAHHAA",
                "AAAAAAAAHAAAHAHAA",
                "AAAAAAAAHAAAHHAAA",
                "AAAAAAAHAAAAAHHAA",
                "AAAAAAAHAAAAHAHAA",
                "AAAAAAAHAAAAHHAAA",
                "AAAAAAHAAAAAAHHAA",
                "AAAAAAHAAAAAHAHAA",
                "AAAAAAHAAAAAHHAAA",
                "AAAAAHAAAAAAAHHAA",
                "AAAAAHAAAAAAHAHAA",
                "AAAAAHAAAAAAHHAAA",
            ),
        )
        self.assertEqual(len(shards), 21)
        self.assertEqual(
            tuple(item.complete_path_count for item in shards),
            (
                53912,
                20510,
                27542,
                53912,
                20510,
                27542,
                161736,
                61530,
                82626,
                161736,
                61530,
                82626,
                80868,
                30765,
                41313,
                80868,
                30765,
                41313,
                80868,
                30765,
                41313,
            ),
        )
        self.assertEqual(sum(item.complete_path_count for item in shards), 1274550)
        for index, shard in enumerate(shards):
            self.assertEqual(complete_operation_words(shard), (complete_operation_words(schedule)[index],))
            self.assertTrue(shard.metadata["fixed_target_has_representation"])

    def test_operation_word_projection_partitions_an_independent_toy(self) -> None:
        start = AlignmentState(0, 0, -1)
        left = AlignmentState(1, 0, 0)
        right = AlignmentState(0, 1, 1)
        finish = AlignmentState(1, 1, 0)
        edges = (
            (
                AlignmentTransition(0, start, left, "ADVANCE", 0, 0),
                AlignmentTransition(0, start, right, "HOLD", 0, 1),
            ),
            (
                AlignmentTransition(1, left, finish, "HOLD", 0, 0),
                AlignmentTransition(1, right, finish, "ADVANCE", 0, 0),
            ),
        )
        schedule = CompatibleSchedule(
            "toy",
            1,
            AlignmentAutomaton(((start,), (left, right), (finish,)), edges, edges),
            2,
        )
        words = complete_operation_words(schedule)
        shards = compatible_schedule_operation_word_shards(schedule)
        self.assertEqual(words, (("ADVANCE", "HOLD"), ("HOLD", "ADVANCE")))
        self.assertEqual([item.complete_path_count for item in shards], [1, 1])
        self.assertEqual(sum(item.complete_path_count for item in shards), 2)
        parent_paths = {(edges[0][0], edges[1][0]), (edges[0][1], edges[1][1])}
        shard_path_sets = [
            {(shard.automaton.forward[0][0], shard.automaton.forward[1][0])}
            for shard in shards
        ]
        self.assertEqual(set().union(*shard_path_sets), parent_paths)
        self.assertFalse(shard_path_sets[0] & shard_path_sets[1])
        for word, shard in zip(words, shards, strict=True):
            self.assertEqual(complete_operation_words(shard), (word,))
            with self.assertRaises(ValueError):
                compatible_schedule_for_operation_word(
                    schedule, tuple(reversed(word)) + ("HOLD",)
                )

    def test_affine_two_hold_relocation_stable_counts_and_fixed_target(self) -> None:
        schedule = affine_two_hold_relocation_schedule()
        baseline = tuple(
            edge.operation for edge in affine_schedule_template().transitions
        )
        words_by_state = {schedule.automaton.layers[0][0]: {()}}
        for edges in schedule.automaton.forward:
            following = {}
            for edge in edges:
                following.setdefault(edge.after, set()).update(
                    (*word, edge.operation)
                    for word in words_by_state.get(edge.before, ())
                )
            words_by_state = following
        operation_words = {word for words in words_by_state.values() for word in words}
        self.assertEqual(len(operation_words), 63)
        self.assertEqual(schedule.complete_path_count, 8992170)
        self.assertEqual(
            schedule.layer_state_counts,
            (1, 5, 5, 5, 4, 3, 4, 3, 5, 4, 7, 3, 1, 3, 5, 5, 5, 5),
        )
        self.assertEqual(
            schedule.layer_edge_counts,
            (5, 13, 13, 11, 8, 10, 8, 8, 11, 15, 14, 3, 3, 9, 14, 13, 13),
        )
        for word in operation_words:
            self.assertEqual(
                sum(a == "HOLD" and b == "ADVANCE" for a, b in zip(baseline, word)),
                2,
            )
            self.assertEqual(
                sum(a == "ADVANCE" and b == "HOLD" for a, b in zip(baseline, word)),
                2,
            )
        for state in schedule.automaton.layers[-1]:
            self.assertEqual(
                (state.baseline_hold_removals, state.baseline_advance_insertions),
                (2, 2),
            )
        result = search_bidirectional(
            u_count=179,
            cut=9,
            fixed_target=residue_two_affine_pattern(17),
            schedule=schedule,
        )
        self.assertEqual(result.conclusion, "SAT")
        self.assertEqual(result.witness, tuple(residue_two_affine_pattern(17)))

    def test_affine_witness_is_in_radius_one_fixed_cap_language(self) -> None:
        self.assertTrue(language_membership(residue_two_affine_pattern(17), radius=1))

    def test_affine_schedule_freezes_control_but_not_tube_packets(self) -> None:
        source = residue_two_pattern(14)
        target = residue_two_affine_pattern(17)
        template = affine_schedule_template(source)
        steps = tuple(
            PathStep(
                edge.target_row,
                edge.operation,
                edge.source_row,
                edge.before.cursor,
                edge.seam,
            )
            for edge in template.transitions
        )
        self.assertTrue(schedule_accepts_steps(template, steps))
        for edge, row in zip(template.transitions, target, strict=True):
            self.assertIn(
                row,
                enumerate_domain_rows(source[edge.source_row], edge.seam, radius=1),
            )

        edge = template.transitions[3]
        start = 1 + 3 * edge.seam
        replacement = "..." if target[3][start : start + 3] != "..." else "UUU"
        changed = target[3][:start] + replacement + target[3][start + 3 :]
        self.assertNotEqual(changed, target[3])
        self.assertIn(
            changed,
            enumerate_domain_rows(source[edge.source_row], edge.seam, radius=1),
        )

        self.assertFalse(
            schedule_accepts_steps(
                template, (replace(steps[0], operation="HOLD"), *steps[1:])
            )
        )
        changed_seam = (steps[3].seam + 1) % 5
        self.assertFalse(
            schedule_accepts_steps(
                template,
                (*steps[:3], replace(steps[3], seam=changed_seam), *steps[4:]),
            )
        )

    def test_constrained_affine_search_reconstructs_and_accepts(self) -> None:
        target = residue_two_affine_pattern(17)
        result = search(u_count=179, fixed_target=target)
        self.assertEqual(result.conclusion, "SAT")
        self.assertEqual(result.witness, tuple(target))
        assert result.steps is not None and result.witness is not None
        self.assertEqual(sum(step.operation == "HOLD" for step in result.steps), 3)
        self.assertEqual(sum(step.operation == "ADVANCE" for step in result.steps), 14)
        self.assertEqual(
            [step.source_row for step in result.steps],
            sorted(step.source_row for step in result.steps),
        )
        replay_path(residue_two_pattern(14), result.witness, result.steps, radius=1)
        assert result.validation is not None
        self.assertTrue(result.validation["accepted"])
        self.assertNotIn("run_check", result.validation)

    def test_constrained_affine_bidirectional_join_at_both_cuts(self) -> None:
        target = residue_two_affine_pattern(17)
        for cut in (8, 9):
            result = search_bidirectional(u_count=179, cut=cut, fixed_target=target)
            self.assertEqual(result.conclusion, "SAT")
            self.assertEqual(result.witness, tuple(target))
            self.assertEqual(result.top_stats[-1].depth, cut)
            self.assertEqual(result.bottom_stats[-1].depth, 17 - cut)
            self.assertGreater(result.join_stats.connected_pairs, 0)
            assert result.steps is not None and result.witness is not None
            replay_path(residue_two_pattern(14), result.witness, result.steps, radius=1)
            assert result.validation is not None
            self.assertTrue(result.validation["accepted"])

    @slow_test
    def test_fully_fixed_affine_passes_schedule_forward_and_bidirectional(self) -> None:
        target = residue_two_affine_pattern(17)
        forward = search(u_count=179, fixed_target=target, schedule="affine")
        joined = search_bidirectional(
            u_count=179, cut=8, fixed_target=target, schedule="affine"
        )
        wider = search_bidirectional(
            u_count=179,
            radius=2,
            cut=8,
            fixed_target=target,
            schedule="affine",
        )
        boundary_one = search_bidirectional(
            u_count=179,
            cut=8,
            fixed_target=target,
            schedule="affine",
            boundary_rewrites=1,
        )
        for result in (forward, joined, wider, boundary_one):
            self.assertEqual(result.conclusion, "SAT")
            self.assertEqual(result.witness, tuple(target))
            self.assertEqual(result.schedule, "affine")
            self.assertEqual(result.validation["boundary_rewrites"], 0)
        self.assertEqual(joined.steps, wider.steps)
        self.assertEqual(affine_schedule_template().minimum_radius, 1)
        with self.assertRaisesRegex(ValueError, "below its minimum"):
            search_bidirectional(
                u_count=179,
                radius=0,
                cut=8,
                fixed_target=target,
                schedule="affine",
            )

    def test_small_complete_pattern_bidirectional_join(self) -> None:
        target = residue_two_pattern(8)
        groups = ((0,), (1,), (2, 3), (4, 5, 6), (7,))
        source = [
            target[group[0]][0] + target[group[0]][4:7] + target[group[0]][-1]
            for group in groups
        ]
        result = search_bidirectional(
            source=source,
            target_n=8,
            radius=1,
            u_count=sum(row.count("U") for row in target),
            cut=4,
            fixed_rows=(),
            fixed_target=target,
        )
        self.assertEqual(result.conclusion, "SAT")
        self.assertEqual(result.witness, tuple(target))
        assert result.validation is not None
        self.assertTrue(result.validation["accepted"])
        self.assertTrue(result.validation["run_check"]["all_ok"])

    def test_bucketed_join_matches_legacy_and_cache_on_small_control(self) -> None:
        target = residue_two_pattern(8)
        groups = ((0,), (1,), (2, 3), (4, 5, 6), (7,))
        source = tuple(
            target[group[0]][0] + target[group[0]][4:7] + target[group[0]][-1]
            for group in groups
        )
        budget = sum(row.count("U") for row in target)
        frontiers = build_bidirectional_frontiers(
            source=source,
            target_n=8,
            radius=1,
            u_limit=budget,
            cut=4,
            fixed_rows=(),
            fixed_target=target,
        )
        legacy = join_bidirectional_frontiers(
            frontiers, u_count=budget, bucketed=False, use_cache=False
        )
        bucketed = join_bidirectional_frontiers(
            frontiers, u_count=budget, bucketed=True, use_cache=False
        )
        cached = join_bidirectional_frontiers(
            frontiers, u_count=budget, bucketed=True, use_cache=True
        )
        fields = (
            "candidate_state_pairs",
            "cost_pruned_pairs",
            "merged_pairs",
            "connected_pairs",
        )
        for field in fields:
            self.assertEqual(
                getattr(legacy.join_stats, field), getattr(bucketed.join_stats, field)
            )
            self.assertEqual(
                getattr(bucketed.join_stats, field), getattr(cached.join_stats, field)
            )
        self.assertEqual(legacy.witness is not None, bucketed.witness is not None)
        self.assertEqual(bucketed.witness is not None, cached.witness is not None)
        self.assertEqual(legacy.witness, bucketed.witness)
        self.assertEqual(bucketed.witness, cached.witness)
        self.assertEqual(
            legacy.join_stats.merge_evaluations, legacy.join_stats.merged_pairs
        )
        self.assertEqual(
            cached.join_stats.cache_hits + cached.join_stats.merge_evaluations,
            cached.join_stats.merged_pairs,
        )

    def test_boundary_lanes_scope_and_join_modes_are_exact(self) -> None:
        target = list(residue_two_pattern(8))
        groups = ((0,), (1,), (2, 3), (4, 5, 6), (7,))
        source = tuple(
            target[group[0]][0] + target[group[0]][4:7] + target[group[0]][-1]
            for group in groups
        )
        toggle = {".": "U", "U": "."}
        for row in (0, 7):
            target[row] = toggle[target[row][0]] + target[row][1:]
        frontiers = build_bidirectional_frontiers(
            source=source,
            target_n=8,
            radius=1,
            u_limit=100,
            cut=4,
            fixed_rows=(),
            fixed_target=target,
            boundary_rewrites=1,
        )
        top_one = sum(node.boundary_rewrites == 1 for node in frontiers.top)
        bottom_one = sum(node.boundary_rewrites == 1 for node in frontiers.bottom)
        self.assertGreater(top_one, 0)
        self.assertGreater(bottom_one, 0)

        expected_scope_prunes = sum(
            top.boundary_rewrites + bottom.boundary_rewrites > 1
            for top in frontiers.top
            for bottom in frontiers.bottom
            if top.alignment == bottom.alignment
        )
        legacy = join_bidirectional_frontiers(
            frontiers,
            u_count=100,
            boundary_rewrites=1,
            bucketed=False,
            use_cache=False,
        )
        bucketed = join_bidirectional_frontiers(
            frontiers,
            u_count=100,
            boundary_rewrites=1,
            bucketed=True,
            use_cache=False,
        )
        cached = join_bidirectional_frontiers(
            frontiers,
            u_count=100,
            boundary_rewrites=1,
            bucketed=True,
            use_cache=True,
        )
        fields = (
            "candidate_state_pairs",
            "scope_pruned_pairs",
            "cost_pruned_pairs",
            "merged_pairs",
            "connected_pairs",
        )
        for field in fields:
            self.assertEqual(
                getattr(legacy.join_stats, field), getattr(bucketed.join_stats, field)
            )
            self.assertEqual(
                getattr(bucketed.join_stats, field), getattr(cached.join_stats, field)
            )
        self.assertEqual(legacy.join_stats.scope_pruned_pairs, expected_scope_prunes)
        self.assertEqual(
            legacy.join_stats.candidate_state_pairs,
            legacy.join_stats.scope_pruned_pairs
            + legacy.join_stats.cost_pruned_pairs
            + legacy.join_stats.merged_pairs,
        )
        self.assertEqual(legacy.witness, bucketed.witness)
        self.assertEqual(bucketed.witness, cached.witness)

    def test_zero_budget_frontiers_and_explicit_join_match_legacy_defaults(
        self,
    ) -> None:
        target = residue_two_pattern(8)
        groups = ((0,), (1,), (2, 3), (4, 5, 6), (7,))
        source = tuple(
            target[group[0]][0] + target[group[0]][4:7] + target[group[0]][-1]
            for group in groups
        )
        options = dict(
            source=source,
            target_n=8,
            radius=1,
            u_limit=100,
            cut=4,
            fixed_rows=(),
            fixed_target=target,
        )
        default = build_bidirectional_frontiers(**options)
        explicit = build_bidirectional_frontiers(**options, boundary_rewrites=0)
        self.assertEqual(
            [(exact_state_key(node), node.state.u_cost) for node in default.top],
            [(exact_state_key(node), node.state.u_cost) for node in explicit.top],
        )
        self.assertEqual(
            [(exact_state_key(node), node.state.u_cost) for node in default.bottom],
            [(exact_state_key(node), node.state.u_cost) for node in explicit.bottom],
        )
        legacy = join_bidirectional_frontiers(default, u_count=100)
        declared = join_bidirectional_frontiers(
            explicit, u_count=100, boundary_rewrites=0
        )
        self.assertEqual(legacy.witness, declared.witness)
        self.assertEqual(legacy.join_stats, declared.join_stats)

    def test_fixed_toy_needs_exactly_one_boundary_rewrite(self) -> None:
        target = list(residue_two_pattern(8))
        groups = ((0,), (1,), (2, 3), (4, 5, 6), (7,))
        source = tuple(
            target[group[0]][0] + target[group[0]][4:7] + target[group[0]][-1]
            for group in groups
        )
        toggle = {".": "U", "U": "."}
        target[0] = toggle[target[0][0]] + target[0][1:]
        options = dict(
            source=source,
            target_n=8,
            radius=1,
            u_count=100,
            cut=4,
            fixed_rows=(),
            fixed_target=target,
        )
        strict = search_bidirectional(**options, boundary_rewrites=0)
        widened = search_bidirectional(**options, boundary_rewrites=1)
        self.assertEqual(strict.conclusion, "UNSAT_IN_LANGUAGE")
        self.assertEqual(widened.conclusion, "SAT")
        self.assertEqual(widened.witness, tuple(target))
        self.assertEqual(widened.validation["boundary_rewrites"], 1)
        self.assertEqual(widened.boundary_rewrites, 1)

    def test_reused_frontiers_and_join_modes_match_on_affine_control(self) -> None:
        target = residue_two_affine_pattern(17)
        frontiers = build_bidirectional_frontiers(
            u_limit=179,
            cut=9,
            fixed_target=target,
            schedule="affine",
        )
        for budget in (179, 178):
            frontiers.connectivity_cache.clear()
            legacy = join_bidirectional_frontiers(
                frontiers, u_count=budget, bucketed=False, use_cache=False
            )
            bucketed = join_bidirectional_frontiers(
                frontiers, u_count=budget, bucketed=True, use_cache=True
            )
            self.assertEqual(
                (
                    legacy.join_stats.candidate_state_pairs,
                    legacy.join_stats.cost_pruned_pairs,
                    legacy.join_stats.merged_pairs,
                    legacy.join_stats.connected_pairs,
                    legacy.witness is not None,
                ),
                (
                    bucketed.join_stats.candidate_state_pairs,
                    bucketed.join_stats.cost_pruned_pairs,
                    bucketed.join_stats.merged_pairs,
                    bucketed.join_stats.connected_pairs,
                    bucketed.witness is not None,
                ),
            )


if __name__ == "__main__":
    unittest.main()
