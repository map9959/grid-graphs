#!/usr/bin/env python3
"""Observed three-row equality-band classes for residue-two optimum paths.

This is a finite-width replay diagnostic.  It makes no claim about unobserved
optimum paths at widths 11, 14, or 17, or about widths outside the sample.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter, defaultdict
from dataclasses import asdict, dataclass
from pathlib import Path

from diagonal_patterns import residue_two_affine_pattern, residue_two_explicit_pattern
from equality_band_macros import (
    EqualityBandMacroTransition,
    advance_equality_band,
    rooted_debt,
    verify_equality_band_macro,
)
from equality_corridor import build_equality_corridor
from equality_slab_lanes import enumerate_minimum_mask_paths, replay_masks
from tile_grammar import FrontierState, row_mask


SCHEMA = "grid-graphs.residue-two-band-classifier.v1"


@dataclass(frozen=True, slots=True)
class PacketOffsets:
    """Per-row offsets from two U and two vertical edges per 3-column packet."""

    packets: int
    u: tuple[int, int, int]
    vertical_edges: tuple[int, int, int]


@dataclass(frozen=True, slots=True)
class NormalizedBandClass:
    """All requested band facts, with width growth represented by offsets."""

    boundary_role: str
    weight: int
    attachment_debt_delta: int
    out_merge_counts: tuple[int, int, int]
    cycle_delta: int
    rank_offset: int
    u_offsets: tuple[int, int, int]
    vertical_edge_offsets: tuple[int, int, int]


@dataclass(frozen=True, slots=True)
class BandObservation:
    width: int
    path_index: int
    start_row: int
    window_kinds: tuple[str, ...]
    boundary_role: str
    masks: tuple[int, int, int]
    weight: int
    d_u: int
    d_edges: int
    attachment_debt_before: int
    attachment_debt_after: int
    attachment_debt_delta: int
    out_merges: tuple[tuple[int, ...], tuple[int, ...], tuple[int, ...]]
    cycle_delta: int
    rank_delta: int
    packet_offsets: PacketOffsets
    normalized_class: NormalizedBandClass


def boundary_role(width: int, start_row: int) -> str:
    if not 0 <= start_row <= width - 3:
        raise ValueError("three-row window does not fit the path")
    if start_row == 0:
        return "top"
    if start_row + 3 == width:
        return "bottom"
    return "interior"


def normalized_packet_offsets(macro: EqualityBandMacroTransition) -> PacketOffsets:
    """Subtract the row-profile baseline used by equality_corridor.py."""
    packets = macro.incoming.n // 3
    vertical = tuple(
        (row.mask & macro.structural_states[index].previous_u_mask).bit_count()
        for index, row in enumerate(macro.rows)
    )
    return PacketOffsets(
        packets=packets,
        u=tuple(row.d_u - 2 * packets for row in macro.rows),  # type: ignore[arg-type]
        vertical_edges=tuple(value - 2 * packets for value in vertical),  # type: ignore[arg-type]
    )


def _normalized_class(
    macro: EqualityBandMacroTransition, role: str, offsets: PacketOffsets
) -> NormalizedBandClass:
    return NormalizedBandClass(
        boundary_role=role,
        weight=macro.weight,
        attachment_debt_delta=macro.rooted_debt_after - macro.rooted_debt_before,
        out_merge_counts=tuple(
            len(row.rooted_debt.incoming_blocks_merged_into_out) for row in macro.rows
        ),  # type: ignore[arg-type]
        cycle_delta=macro.d_cycles,
        rank_offset=macro.d_rank - 9 * offsets.packets,
        u_offsets=offsets.u,
        vertical_edge_offsets=offsets.vertical_edges,
    )


def classify_masks(masks: tuple[int, ...], path_index: int = 0) -> list[BandObservation]:
    """Replay every valid sliding window and tag phase-aligned windows."""
    states = replay_masks(masks)
    observations = []
    for start in range(len(masks) - 2):
        macro = advance_equality_band(states[start], masks[start : start + 3])
        if macro is None:
            raise AssertionError(f"accepted path produced a rejected band at row {start}")
        verify_equality_band_macro(macro)
        if macro.outgoing != states[start + 3]:
            raise AssertionError("macro replay disagrees with the full path replay")
        role = boundary_role(len(masks), start)
        offsets = normalized_packet_offsets(macro)
        kinds = ("sliding", "aligned") if start % 3 == 0 else ("sliding",)
        observations.append(
            BandObservation(
                width=len(masks),
                path_index=path_index,
                start_row=start,
                window_kinds=kinds,
                boundary_role=role,
                masks=macro.masks,
                weight=macro.weight,
                d_u=macro.d_u,
                d_edges=macro.d_edges,
                attachment_debt_before=macro.rooted_debt_before,
                attachment_debt_after=macro.rooted_debt_after,
                attachment_debt_delta=macro.rooted_debt_after - macro.rooted_debt_before,
                out_merges=tuple(
                    row.rooted_debt.incoming_blocks_merged_into_out for row in macro.rows
                ),  # type: ignore[arg-type]
                cycle_delta=macro.d_cycles,
                rank_delta=macro.d_rank,
                packet_offsets=offsets,
                normalized_class=_normalized_class(macro, role, offsets),
            )
        )
    return observations


def class_id(value: NormalizedBandClass) -> str:
    payload = json.dumps(asdict(value), sort_keys=True, separators=(",", ":"))
    return "B" + hashlib.sha256(payload.encode("ascii")).hexdigest()[:16]


def _state_vertex(state: FrontierState) -> tuple:
    """Observed graph vertex; deliberately omits absolute width and row depth."""
    if state.row_index == 0:
        role = "top"
    elif state.row_index == state.n:
        role = "closed"
    else:
        role = "open"
    packets = state.n // 3
    return (
        role,
        state.row_index % 3,
        state.previous_u_mask.bit_count() - 2 * packets,
        rooted_debt(state),
        state.cycle_excess,
    )


def _scc_stats(edges: set[tuple[tuple, tuple]]) -> dict:
    vertices = {vertex for edge in edges for vertex in edge}
    adjacency: dict[tuple, set[tuple]] = defaultdict(set)
    for left, right in edges:
        adjacency[left].add(right)
    index = 0
    indices = {}
    low = {}
    stack = []
    on_stack = set()
    components = []

    def visit(vertex: tuple) -> None:
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

    for vertex in sorted(vertices, key=repr):
        if vertex not in indices:
            visit(vertex)
    loops = {left for left, right in edges if left == right}
    cyclic = [part for part in components if len(part) > 1 or part[0] in loops]
    return {
        "vertices": len(vertices),
        "edges": len(edges),
        "strong_components": len(components),
        "nontrivial_strong_components": len(cyclic),
        "vertices_in_nontrivial_strong_components": sum(map(len, cyclic)),
        "self_loops": len(loops),
    }


def _sources() -> list[tuple[str, int, str, list[tuple[int, ...]]]]:
    sources = []
    for n in (5, 8):
        paths = enumerate_minimum_mask_paths(build_equality_corridor(n))
        sources.append((f"n{n}-exact-corridor", n, "all-optimum-paths", paths))
    for n, rows in (
        (11, residue_two_explicit_pattern(11)),
        (14, residue_two_explicit_pattern(14)),
        (17, residue_two_affine_pattern(17)),
    ):
        sources.append((f"n{n}-fixed-witness", n, "one-fixed-witness", [tuple(map(row_mask, rows))]))
    return sources


def build_artifact() -> dict:
    supports: dict[int, set[NormalizedBandClass]] = {}
    class_values: dict[str, NormalizedBandClass] = {}
    source_records = {}
    graph_edges = set()
    total_observations = 0
    for name, width, selection, paths in _sources():
        counts = Counter()
        support = set()
        aligned = 0
        roles = Counter()
        for path_index, masks in enumerate(paths):
            states = replay_masks(masks)
            observations = classify_masks(masks, path_index)
            total_observations += len(observations)
            for observation in observations:
                identifier = class_id(observation.normalized_class)
                previous = class_values.setdefault(identifier, observation.normalized_class)
                if previous != observation.normalized_class:
                    raise AssertionError("truncated normalized-class hash collision")
                counts[identifier] += 1
                support.add(observation.normalized_class)
                aligned += "aligned" in observation.window_kinds
                roles[observation.boundary_role] += 1
                graph_edges.add(
                    (_state_vertex(states[observation.start_row]), _state_vertex(states[observation.start_row + 3]))
                )
        supports[width] = support
        source_records[name] = {
            "width": width,
            "selection": selection,
            "paths": len(paths),
            "sliding_windows": sum(counts.values()),
            "aligned_windows": aligned,
            "normalized_classes": len(support),
            "boundary_role_histogram": dict(sorted(roles.items())),
        }

    recurring = {
        band_class: tuple(
            width for width, support in supports.items() if band_class in support
        )
        for band_class in class_values.values()
        if sum(band_class in support for support in supports.values()) > 1
    }
    recurring_records = [
        {
            "class_id": class_id(band_class),
            "widths": list(widths),
            "class": json.loads(json.dumps(asdict(band_class))),
        }
        for band_class, widths in sorted(recurring.items(), key=lambda item: repr(item[0]))
    ]
    return {
        "schema": SCHEMA,
        "scope": {
            "semantics": "observed-three-row-macro-replay-diagnostic-only",
            "widths": [5, 8, 11, 14, 17],
            "complete_optimum_path_widths": [5, 8],
            "fixed_witness_widths": [11, 14, 17],
            "coverage_beyond_listed_paths_claimed": False,
        },
        "definitions": {
            "sliding_window": "every start row 0 through n-3",
            "aligned_window": "a sliding window whose zero-based start row is divisible by three",
            "boundary_role": "top at row 0, bottom at row n-3, interior otherwise",
            "attachment_debt": "number of live frontier components not containing OUT",
            "out_merges": "exact incoming non-OUT partition labels joined to OUT, retained per primitive row",
            "packet_offsets": "per-row dU and vertical-edge count minus 2*floor(n/3)",
            "rank_offset": "three-row rank delta minus 9*floor(n/3), the value compatible with the six-U packet baseline and fixed band weight",
            "complete_normalized_class": "boundary role, weight, debt delta, per-row OUT-merge counts, cycle delta, rank offset, and all packet offsets",
        },
        "sources": source_records,
        "census": {
            "sliding_window_observations": total_observations,
            "normalized_classes": len(class_values),
            "recurring_complete_normalized_classes": len(recurring_records),
            "any_complete_normalized_class_recurs": bool(recurring_records),
        },
        "recurring_complete_normalized_classes": recurring_records,
        "observed_graph": {
            "provenance": "one edge per replayed sliding macro endpoint, deduplicated after pooling only the listed sources",
            "vertex_definition": [
                "boundary mode",
                "row phase modulo 3",
                "previous-row U count minus 2*floor(n/3)",
                "rooted attachment debt",
                "cumulative cycle excess",
            ],
            "warning": "pooled observed edges need not compose as paths; SCCs are not a global recurrence claim",
            **_scc_stats(graph_edges),
        },
        "provenance": {
            "producer": "analysis/residue_two_band_classifier.py",
            "command": [
                "python3", "-B", "analysis/residue_two_band_classifier.py",
                "--output", "analysis/residue_two_band_classifier.json",
            ],
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    rendered = json.dumps(build_artifact(), indent=2, sort_keys=True) + "\n"
    if args.output is not None:
        args.output.write_text(rendered)
    print(rendered, end="")


if __name__ == "__main__":
    main()
