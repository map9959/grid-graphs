#!/usr/bin/env python3
"""Census concrete width-three slab/band lifts between equality corridors."""

from __future__ import annotations

import argparse
import json
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path

from equality_corridor import EqualityCorridor, build_equality_corridor
from tile_grammar import (
    FrontierState,
    advance_row,
    canonicalize_partition_labels,
    compress_mask,
    initial_state,
)


SCHEMA = "grid-graphs.equality-slab-lanes.v1"


@dataclass(frozen=True, slots=True)
class CrossSlabSignature:
    compressed_previous_u_mask: int
    slab_previous_u_mask: int
    projected_partition: tuple[int, ...]
    attachment_partition: tuple[int, ...]
    normalized_u_cost: int
    cycle_excess: int


def enumerate_minimum_mask_paths(corridor: EqualityCorridor) -> list[tuple[int, ...]]:
    adjacency = []
    for edges in corridor.corridor_edges:
        by_incoming = defaultdict(list)
        for edge in edges:
            by_incoming[edge.incoming].append(edge)
        adjacency.append(by_incoming)

    paths = []

    def visit(row: int, key, masks: tuple[int, ...]) -> None:
        if row == corridor.n:
            paths.append(masks)
            return
        for edge in adjacency[row][key]:
            visit(row + 1, edge.outgoing, (*masks, edge.mask))

    initial_key = next(iter(corridor.layers[0]))
    visit(0, initial_key, ())
    if len(paths) != corridor.minimum_path_count or len(set(paths)) != len(paths):
        raise AssertionError("minimum path enumeration disagrees with corridor count")
    return paths


def replay_masks(masks: tuple[int, ...]) -> list[FrontierState]:
    state = initial_state(len(masks))
    trace = [state]
    for mask in masks:
        outgoing = advance_row(state, mask)
        if outgoing is None:
            raise ValueError("mask path is not dual-connected")
        state = outgoing
        trace.append(state)
    return trace


def delete_band_and_slab(
    masks: tuple[int, ...], band_start: int, slab_start: int
) -> tuple[int, ...]:
    n = len(masks)
    if n < 5 or not 0 <= band_start <= n - 3 or not 0 <= slab_start <= n - 3:
        raise ValueError("band or open-slab position does not fit the square path")
    return tuple(
        compress_mask(mask, slab_start, 3)
        for row, mask in enumerate(masks)
        if not band_start <= row < band_start + 3
    )


def extract_cross_slab_signature(
    state: FrontierState,
    vertex_slab_start: int,
    removed_u_cost: int,
    slab_width: int = 3,
) -> CrossSlabSignature:
    """Project deleted vertex columns and their adjacent face ports."""
    if slab_width <= 0:
        raise ValueError("cross-slab width must be positive")
    if (
        len(state.partition) != state.n
        or not 0 <= vertex_slab_start <= state.n - slab_width
    ):
        raise ValueError("cross-slab projection requires a full frontier and valid slab")
    if not 0 <= removed_u_cost <= state.u_cost:
        raise ValueError("removed U cost is outside the processed prefix")
    face_slab_start = min(vertex_slab_start, state.n - slab_width - 1)
    hidden = set(
        range(1 + face_slab_start, 1 + face_slab_start + slab_width)
    )
    retained_indices = [index for index in range(state.n) if index not in hidden]
    retained_labels = tuple(state.partition[index] for index in retained_indices)
    projected_partition = canonicalize_partition_labels(retained_labels)
    projected_count = len(set(projected_partition))
    original_by_projected = [None] * projected_count
    for projected, original in zip(projected_partition, retained_labels, strict=True):
        if original_by_projected[projected] is None:
            original_by_projected[projected] = original
    hidden_labels = tuple(state.partition[index] for index in sorted(hidden))
    return CrossSlabSignature(
        compressed_previous_u_mask=compress_mask(
            state.previous_u_mask, vertex_slab_start, slab_width
        ),
        slab_previous_u_mask=(state.previous_u_mask >> vertex_slab_start)
        & ((1 << slab_width) - 1),
        projected_partition=projected_partition,
        attachment_partition=canonicalize_partition_labels(
            (*original_by_projected, *hidden_labels)
        ),
        normalized_u_cost=state.u_cost - removed_u_cost,
        cycle_excess=state.cycle_excess,
    )


def known_large_trace_deletions() -> dict:
    from diagonal_patterns import residue_two_affine_pattern, residue_two_explicit_pattern
    from tile_grammar import row_mask

    source = tuple(map(row_mask, residue_two_explicit_pattern(14)))
    target = tuple(map(row_mask, residue_two_affine_pattern(17)))
    matches = []
    for band_start in range(15):
        for slab_start in range(15):
            if delete_band_and_slab(target, band_start, slab_start) == source:
                matches.append(
                    {"band_start": band_start, "slab_start": slab_start}
                )
    return {
        "source_n": 14,
        "target_n": 17,
        "deletions_tested": 15 * 15,
        "exact_deletion_matches": matches,
    }


def mapped_target_depths(source_depth: int, band_start: int) -> tuple[int, ...]:
    if source_depth < band_start:
        return (source_depth,)
    if source_depth == band_start:
        return (band_start, band_start + 3)
    return (source_depth + 3,)


def removed_prefix_u(
    target_masks: tuple[int, ...], target_depth: int, band_start: int, slab_start: int
) -> int:
    slab_mask = 0b111 << slab_start
    removed = 0
    for row, mask in enumerate(target_masks[:target_depth]):
        if band_start <= row < band_start + 3:
            removed += mask.bit_count()
        else:
            removed += (mask & slab_mask).bit_count()
    return removed


def _forgotten_only_components(signature) -> tuple[int, ...]:
    projected_count = len(set(signature.projected_partition))
    visible = set(signature.attachment_partition[:projected_count])
    hidden = set(signature.attachment_partition[projected_count:])
    return tuple(sorted(hidden - visible))


def audit_lane(
    source_masks: tuple[int, ...],
    target_masks: tuple[int, ...],
    band_start: int,
    slab_start: int,
) -> dict:
    source_trace = replay_masks(source_masks)
    target_trace = replay_masks(target_masks)
    comparisons = []
    structural = cost = no_forgotten = cycle_preserving = True
    for source_depth in range(1, 5):
        for target_depth in mapped_target_depths(source_depth, band_start):
            if not 1 <= target_depth <= 7:
                continue
            source = source_trace[source_depth]
            target = target_trace[target_depth]
            removed_u = removed_prefix_u(
                target_masks, target_depth, band_start, slab_start
            )
            signature = extract_cross_slab_signature(target, slab_start, removed_u)
            forgotten = _forgotten_only_components(signature)
            structural_match = (
                signature.compressed_previous_u_mask == source.previous_u_mask
                and signature.projected_partition == source.partition
            )
            cost_match = signature.normalized_u_cost == source.u_cost
            cycle_match = signature.cycle_excess == source.cycle_excess
            structural &= structural_match
            cost &= cost_match
            no_forgotten &= not forgotten
            cycle_preserving &= cycle_match
            comparisons.append(
                {
                    "source_depth": source_depth,
                    "target_depth": target_depth,
                    "structural_match": structural_match,
                    "cost_match": cost_match,
                    "cycle_match": cycle_match,
                    "cycle_delta": signature.cycle_excess - source.cycle_excess,
                    "forgotten_only_components": list(forgotten),
                    "removed_u": removed_u,
                    "slab_previous_u_mask": signature.slab_previous_u_mask,
                    "attachment_partition": list(signature.attachment_partition),
                }
            )
    total_removed = sum(mask.bit_count() for mask in target_masks) - sum(
        mask.bit_count() for mask in source_masks
    )
    direct_removed = removed_prefix_u(target_masks, 8, band_start, slab_start)
    if total_removed != direct_removed:
        raise AssertionError("band/slab union deletion cost is inconsistent")
    terminal_cycle_delta = (
        target_trace[-1].cycle_excess - source_trace[-1].cycle_excess
    )
    cycle_preserving &= terminal_cycle_delta == 0
    return {
        "structural_match": structural,
        "cost_match": cost,
        "no_forgotten_components": no_forgotten,
        "cycle_preserving": cycle_preserving,
        "terminal_cycle_delta": terminal_cycle_delta,
        "visible_interface_match": structural and cost,
        "closed_projection_match": structural and cost and no_forgotten,
        "removed_u": direct_removed,
        "comparisons": comparisons,
    }


def _path_weights(masks: tuple[int, ...]) -> list[int]:
    trace = replay_masks(masks)
    weights = []
    for row, mask in enumerate(masks):
        incoming = trace[row]
        outgoing = trace[row + 1]
        d_u = outgoing.u_cost - incoming.u_cost
        d_cycles = outgoing.cycle_excess - incoming.cycle_excess
        d_edges = (incoming.previous_u_mask & mask).bit_count() + (
            mask & (mask >> 1)
        ).bit_count()
        weights.append(3 * d_u - 2 * (d_edges - d_cycles) - 1)
    return weights


def _decoration_key(candidate: dict) -> str | None:
    band_start = candidate["band_start"]
    if not 1 <= band_start <= 4:
        return None
    interfaces = [
        item
        for item in candidate["comparisons"]
        if item["source_depth"] == band_start
    ]
    if len(interfaces) != 2:
        raise AssertionError("interior band does not have two decorated interfaces")
    return json.dumps(
        [
            {
                "slab_mask": item["slab_previous_u_mask"],
                "attachment": item["attachment_partition"],
                "forgotten": item["forgotten_only_components"],
                "cycle_delta": item["cycle_delta"],
            }
            for item in interfaces
        ],
        separators=(",", ":"),
    )


def _compact_lane_sample(candidate: dict) -> dict:
    key = _decoration_key(candidate)
    return {
        field: candidate[field]
        for field in (
            "source_path",
            "target_path",
            "band_start",
            "slab_start",
            "inserted_row_masks",
            "inserted_band_weight",
            "cycle_preserving",
            "removed_u",
        )
    } | {"decorated_interfaces": json.loads(key) if key is not None else None}


def _decoration_graph_stats(decoration_counts: Counter[str]) -> dict:
    adjacency = defaultdict(set)
    vertices = set()
    stable_cycle_offset_lanes = 0
    self_loop_lanes = 0
    for key, count in decoration_counts.items():
        upper, lower = json.loads(key)
        upper_key = json.dumps(upper, sort_keys=True, separators=(",", ":"))
        lower_key = json.dumps(lower, sort_keys=True, separators=(",", ":"))
        vertices.update((upper_key, lower_key))
        adjacency[upper_key].add(lower_key)
        stable_cycle_offset_lanes += count * (
            upper["cycle_delta"] == lower["cycle_delta"]
        )
        self_loop_lanes += count * (upper_key == lower_key)

    cycle_vertices = 0
    for start in vertices:
        stack = list(adjacency[start])
        seen = set()
        while stack:
            vertex = stack.pop()
            if vertex == start:
                cycle_vertices += 1
                break
            if vertex not in seen:
                seen.add(vertex)
                stack.extend(adjacency[vertex])
    return {
        "vertices": len(vertices),
        "edges": len(decoration_counts),
        "cycle_offset_stable_lanes": stable_cycle_offset_lanes,
        "self_loop_lanes": self_loop_lanes,
        "vertices_on_directed_cycles": cycle_vertices,
    }


def build_census() -> dict:
    source_corridor = build_equality_corridor(5)
    target_corridor = build_equality_corridor(8)
    source_paths = enumerate_minimum_mask_paths(source_corridor)
    target_paths = enumerate_minimum_mask_paths(target_corridor)
    source_lookup = {path: index for index, path in enumerate(source_paths)}
    candidates = []
    outcome_counts = Counter()
    lane_counts = Counter()
    for target_id, target in enumerate(target_paths):
        for band_start in range(6):
            for slab_start in range(6):
                deleted = delete_band_and_slab(target, band_start, slab_start)
                source_id = source_lookup.get(deleted)
                if source_id is None:
                    continue
                audit = audit_lane(
                    source_paths[source_id], target, band_start, slab_start
                )
                target_weights = _path_weights(target)
                key = (
                    audit["structural_match"],
                    audit["cost_match"],
                    audit["no_forgotten_components"],
                    audit["cycle_preserving"],
                )
                outcome_counts[str(key)] += 1
                if audit["visible_interface_match"]:
                    lane_counts[f"band={band_start},slab={slab_start}"] += 1
                candidates.append(
                    {
                        "source_path": source_id,
                        "target_path": target_id,
                        "band_start": band_start,
                        "slab_start": slab_start,
                        "inserted_row_masks": list(target[band_start : band_start + 3]),
                        "inserted_band_weight": sum(
                            target_weights[band_start : band_start + 3]
                        ),
                        **audit,
                    }
                )

    visible_lanes = [item for item in candidates if item["visible_interface_match"]]
    interior_lanes = [item for item in visible_lanes if 1 <= item["band_start"] <= 4]
    closed_lanes = [item for item in visible_lanes if item["closed_projection_match"]]
    cycle_lanes = [item for item in visible_lanes if item["cycle_preserving"]]
    band_weight_histogram = Counter(item["inserted_band_weight"] for item in visible_lanes)
    decoration_counts = Counter(
        key for item in visible_lanes if (key := _decoration_key(item)) is not None
    )
    sample_by_class = {}
    for item in visible_lanes:
        key = (
            item["band_start"],
            item["slab_start"],
            item["inserted_band_weight"],
            item["cycle_preserving"],
        )
        sample_by_class.setdefault(key, item)
    return {
        "schema": SCHEMA,
        "scope": {
            "source_n": 5,
            "target_n": 8,
            "deleted_rows": 3,
            "deleted_columns": 3,
            "semantics": "complete-minimum-path-cross-deletion-census",
        },
        "census": {
            "source_paths": len(source_paths),
            "target_paths": len(target_paths),
            "deletions_tested": len(target_paths) * 6 * 6,
            "direct_optimum_deletions": len(candidates),
            "visible_interface_lanes": len(visible_lanes),
            "interior_visible_lanes": len(interior_lanes),
            "closed_projection_lanes": len(closed_lanes),
            "cycle_preserving_visible_lanes": len(cycle_lanes),
            "cycle_preserving_interior_lanes": sum(
                item["cycle_preserving"] for item in interior_lanes
            ),
            "outcome_counts": dict(sorted(outcome_counts.items())),
            "visible_lane_counts": dict(sorted(lane_counts.items())),
            "inserted_band_weight_histogram": {
                str(weight): count for weight, count in sorted(band_weight_histogram.items())
            },
            "interior_decorated_interface_classes": len(decoration_counts),
            "decoration_transport_graph": _decoration_graph_stats(decoration_counts),
        },
        "decorated_interface_classes": [
            {"interfaces": json.loads(key), "count": count}
            for key, count in sorted(decoration_counts.items())
        ],
        "visible_lane_samples": [
            _compact_lane_sample(item) for item in sample_by_class.values()
        ],
        "known_large_trace_control": known_large_trace_deletions(),
        "provenance": {
            "producer": "analysis/equality_slab_lanes.py",
            "command": [
                "python3",
                "-B",
                "analysis/equality_slab_lanes.py",
                "--output",
                "analysis/equality_slab_lanes.json",
            ],
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    artifact = build_census()
    rendered = json.dumps(artifact, indent=2) + "\n"
    if args.output is not None:
        args.output.write_text(rendered)
    print(rendered, end="")


if __name__ == "__main__":
    main()
