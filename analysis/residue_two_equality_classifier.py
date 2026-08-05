#!/usr/bin/env python3
"""Finite-width rooted-debt classifier for selected residue-two equality paths.

This is a diagnostic over enumerated corridors and fixed witnesses, not a
theorem, a certificate, or a coverage claim for paths outside that sample.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter, defaultdict
from dataclasses import asdict, dataclass
from pathlib import Path

from diagonal_patterns import residue_two_affine_pattern, residue_two_explicit_pattern
from equality_corridor import _edge, build_equality_corridor, structural_key
from equality_slab_lanes import enumerate_minimum_mask_paths
from tile_grammar import FrontierState, advance_row, initial_state, row_mask


SCHEMA = "grid-graphs.residue-two-equality-debt-classifier.v1"


def canonical_rooted_partition(partition: tuple[int, ...]) -> tuple[int, ...]:
    """Canonicalize labels while forcing the first (OUT) block to label zero."""
    if not partition:
        raise ValueError("a rooted partition must contain OUT")
    labels = {partition[0]: 0}
    result = []
    for label in partition:
        if label not in labels:
            labels[label] = len(labels)
        result.append(labels[label])
    return tuple(result)


@dataclass(frozen=True, slots=True)
class RootedDebt:
    """A finite-width class; cumulative U cost is deliberately not a class key."""

    width: int
    boundary_mode: str
    row_phase: int
    previous_u_mask: int
    rooted_partition: tuple[int, ...]
    out_coverage_bits: tuple[int, int, int, int]
    closure_bits: tuple[int, int, int]
    unresolved_components: int
    cycle_excess: int
    attachment_debt: int
    decorated_debt: int

    @classmethod
    def from_state(cls, state: FrontierState) -> RootedDebt:
        partition = canonical_rooted_partition(state.partition)
        if state.row_index == 0:
            mode = "top"
        elif state.row_index == state.n:
            mode = "closed"
        else:
            mode = "open"

        faces = partition[1:]
        out_faces = tuple(label == 0 for label in faces)
        any_out = any(out_faces)
        all_out = bool(out_faces) and all(out_faces)
        coverage = (
            int(any_out),
            int(bool(out_faces) and out_faces[0]),
            int(bool(out_faces) and out_faces[-1]),
            int(all_out),
        )
        unresolved = len(set(faces) - {0})
        closure = (
            int(unresolved > 0),
            int(unresolved > 1),
            int(mode == "closed" and unresolved == 0),
        )
        # Keep connectivity debt and irreversible cycle excess as distinct
        # channels. Their sum is retained only as a diagnostic decoration.
        return cls(
            width=state.n,
            boundary_mode=mode,
            row_phase=state.row_index % 3,
            previous_u_mask=state.previous_u_mask,
            rooted_partition=partition,
            out_coverage_bits=coverage,
            closure_bits=closure,
            unresolved_components=unresolved,
            cycle_excess=state.cycle_excess,
            attachment_debt=unresolved,
            decorated_debt=unresolved + state.cycle_excess,
        )


def class_id(debt: RootedDebt) -> str:
    payload = json.dumps(asdict(debt), sort_keys=True, separators=(",", ":"))
    return "D" + hashlib.sha256(payload.encode("ascii")).hexdigest()[:16]


@dataclass(frozen=True, slots=True)
class DebtTransition:
    incoming: str
    outgoing: str
    row_phase: int
    row_weight: int
    band_weight: int | None
    cycle_delta: int
    attachment_debt_delta: int
    decorated_debt_delta: int


def classify_masks(masks: tuple[int, ...]) -> tuple[list[RootedDebt], list[DebtTransition], int]:
    """Replay one square path and classify states and weighted row transitions."""
    state = initial_state(len(masks))
    classes = [RootedDebt.from_state(state)]
    transitions = []
    recent_weights: list[int] = []
    total = 0
    for index, mask in enumerate(masks):
        outgoing = advance_row(state, mask)
        if outgoing is None:
            raise ValueError(f"path seals a dual component at row {index}")
        edge = _edge(index, structural_key(state), state, mask, outgoing)
        recent_weights.append(edge.weight)
        if len(recent_weights) > 3:
            recent_weights.pop(0)
        incoming_debt = classes[-1]
        outgoing_debt = RootedDebt.from_state(outgoing)
        transitions.append(
            DebtTransition(
                incoming=class_id(incoming_debt),
                outgoing=class_id(outgoing_debt),
                row_phase=(index + 1) % 3,
                row_weight=edge.weight,
                band_weight=sum(recent_weights) if len(recent_weights) == 3 else None,
                cycle_delta=edge.d_cycles,
                attachment_debt_delta=(
                    outgoing_debt.attachment_debt - incoming_debt.attachment_debt
                ),
                decorated_debt_delta=(
                    outgoing_debt.decorated_debt - incoming_debt.decorated_debt
                ),
            )
        )
        classes.append(outgoing_debt)
        total += edge.weight
        state = outgoing
    if state.partition != (0,):
        raise AssertionError("classified path did not close into OUT")
    return classes, transitions, total


def _strong_components(edges: set[tuple[str, str]]) -> dict:
    vertices = {vertex for edge in edges for vertex in edge}
    adjacency: dict[str, set[str]] = defaultdict(set)
    for incoming, outgoing in edges:
        adjacency[incoming].add(outgoing)

    index = 0
    indices: dict[str, int] = {}
    low: dict[str, int] = {}
    stack: list[str] = []
    on_stack: set[str] = set()
    components: list[list[str]] = []

    def visit(vertex: str) -> None:
        nonlocal index
        indices[vertex] = low[vertex] = index
        index += 1
        stack.append(vertex)
        on_stack.add(vertex)
        for child in adjacency[vertex]:
            if child not in indices:
                visit(child)
                low[vertex] = min(low[vertex], low[child])
            elif child in on_stack:
                low[vertex] = min(low[vertex], indices[child])
        if low[vertex] == indices[vertex]:
            component = []
            while True:
                child = stack.pop()
                on_stack.remove(child)
                component.append(child)
                if child == vertex:
                    break
            components.append(component)

    for vertex in sorted(vertices):
        if vertex not in indices:
            visit(vertex)
    loops = {left for left, right in edges if left == right}
    cyclic = [component for component in components if len(component) > 1 or component[0] in loops]
    return {
        "vertices": len(vertices),
        "edges": len(edges),
        "strong_components": len(components),
        "nontrivial_strong_components": len(cyclic),
        "vertices_in_nontrivial_strong_components": sum(map(len, cyclic)),
        "self_loops": len(loops),
        "acyclic": not cyclic,
    }


def _histogram(values) -> dict[str, int]:
    return {str(key): count for key, count in sorted(Counter(values).items())}


def build_artifact() -> dict:
    """Build the complete census for the two corridors and three witnesses."""
    sources: list[tuple[str, int, str, list[tuple[int, ...]]]] = []
    for n in (5, 8):
        corridor = build_equality_corridor(n)
        sources.append(
            (f"n{n}-exact-corridor", n, "all-minimum-corridor-paths", enumerate_minimum_mask_paths(corridor))
        )
    for n, rows in (
        (11, residue_two_explicit_pattern(11)),
        (14, residue_two_explicit_pattern(14)),
        (17, residue_two_affine_pattern(17)),
    ):
        sources.append((f"n{n}-fixed-witness", n, "one-fixed-witness", [tuple(map(row_mask, rows))]))

    all_classes: dict[str, RootedDebt] = {}
    unique_transitions: set[DebtTransition] = set()
    graph_edges: set[tuple[str, str]] = set()
    source_records = {}
    global_row_weights = Counter()
    global_band_weights = Counter()
    for name, n, kind, paths in sources:
        observed_classes = Counter()
        observed_transitions = Counter()
        totals = Counter()
        source_unique_classes = set()
        source_unique_transitions = set()
        for masks in paths:
            classes, transitions, total = classify_masks(masks)
            totals[total] += 1
            for debt in classes:
                identifier = class_id(debt)
                if identifier in all_classes and all_classes[identifier] != debt:
                    raise AssertionError("truncated class hash collision")
                all_classes[identifier] = debt
                source_unique_classes.add(identifier)
                observed_classes[identifier] += 1
            for transition in transitions:
                unique_transitions.add(transition)
                source_unique_transitions.add(transition)
                graph_edges.add((transition.incoming, transition.outgoing))
                observed_transitions[transition] += 1
                global_row_weights[transition.row_weight] += 1
                if transition.band_weight is not None:
                    global_band_weights[transition.band_weight] += 1
        source_records[name] = {
            "width": n,
            "selection": kind,
            "paths": len(paths),
            "path_total_weights": _histogram(
                total for total, count in totals.items() for _ in range(count)
            ),
            "canonical_classes": len(source_unique_classes),
            "canonical_transitions": len(source_unique_transitions),
            "class_observations": sum(observed_classes.values()),
            "transition_observations": sum(observed_transitions.values()),
        }

    expected = {
        "n5-exact-corridor": {"5": 242},
        "n8-exact-corridor": {"5": 704},
        "n11-fixed-witness": {"5": 1},
        "n14-fixed-witness": {"5": 1},
        "n17-fixed-witness": {"8": 1},
    }
    actual = {name: record["path_total_weights"] for name, record in source_records.items()}
    if actual != expected:
        raise AssertionError(f"control path weights changed: {actual!r}")

    return {
        "schema": SCHEMA,
        "scope": {
            "semantics": "finite-width-enumerated-path-diagnostic-only",
            "widths": [5, 8, 11, 14, 17],
            "corridors": [5, 8],
            "fixed_witnesses": [11, 14, 17],
            "coverage_beyond_enumerated_paths_claimed": False,
            "theorem_or_certificate": False,
        },
        "definition": {
            "root": "partition token 0 is OUT after OUT-first canonical relabeling",
            "out_coverage_bits": ["any_face", "left_face", "right_face", "all_faces"],
            "closure_bits": ["has_unresolved", "multiple_unresolved", "terminally_closed"],
            "attachment_debt": "number of unresolved non-OUT frontier components",
            "decorated_debt": "attachment debt + cumulative cycle excess; diagnostic only",
            "row_weight": "3*dU - 2*dRank - 1",
            "band_weight": "sum of the current and preceding two row weights; absent before row 3",
        },
        "sources": source_records,
        "census": {
            "canonical_classes": len(all_classes),
            "canonical_transitions": len(unique_transitions),
            "class_observations": sum(record["class_observations"] for record in source_records.values()),
            "transition_observations": sum(record["transition_observations"] for record in source_records.values()),
            "row_weight_histogram": {str(k): v for k, v in sorted(global_row_weights.items())},
            "band_weight_histogram": {str(k): v for k, v in sorted(global_band_weights.items())},
            "attachment_debt_histogram": _histogram(
                debt.attachment_debt for debt in all_classes.values()
            ),
            "decorated_debt_histogram": _histogram(
                debt.decorated_debt for debt in all_classes.values()
            ),
            "cycle_excess_histogram": _histogram(debt.cycle_excess for debt in all_classes.values()),
        },
        "quotient_graph": _strong_components(graph_edges),
        "provenance": {
            "producer": "analysis/residue_two_equality_classifier.py",
            "command": [
                "python3", "-B", "analysis/residue_two_equality_classifier.py",
                "--output", "analysis/residue_two_equality_classifier.json",
            ],
        },
        "limitations": [
            "Only all minimum paths at widths 5 and 8 and one fixed witness at each larger width are sampled.",
            "The width and exact frontier word remain in the class, so this is not a width-independent quotient.",
            "Attachment and decorated debt are descriptors, not proved lower bounds or potential inequalities.",
            "SCC diagnostics concern only observed transitions; absence of a cycle is not a global acyclicity result.",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    rendered = json.dumps(build_artifact(), indent=2) + "\n"
    if args.output is not None:
        args.output.write_text(rendered)
    print(rendered, end="")


if __name__ == "__main__":
    main()
